module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Desc4
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} {IsK : GroupClass}
  {S Up Lo : List TauCeti.SporadicName} {R : GroupClass}

theorem not_sporadic_of_isK_quot (rc : ReachFacts IsK S Up Lo R) {P : Subgroup H}
    (hPq : CFSG.IsQuasisimple ↥P) (hK : IsK (↥P ⧸ CFSG.oddCore ↥P)) :
    ¬ ∃ s ∈ S ++ Up, IsSporadic (↥P ⧸ center ↥P) s := by
  have : Group.IsPerfect ↥P := hPq.1
  obtain ⟨e⟩ := cqEquiv_of_cover (QuotientGroup.mk' (CFSG.oddCore ↥P))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact oddCore_le_center hPq)
  rintro ⟨s', hs', ⟨f⟩⟩
  exact rc.K_not_sporadic _ hK s' hs' ⟨e.symm.trans f⟩

theorem false_of_klike_maximal (c : DescCtx H N IsK S Up Lo R) {L₀ : Subgroup H}
    (hL₀ : InL L₀) (hL₀t : ∃ s ∈ S, OddCover s L₀) {P : Subgroup H} (hmax : Maximal P)
    (hPK : KLike IsK P) : False := by
  have := c.hN.normal
  have hlow := klike_hlow c.rc hmax.1.isQuasisimple hPK
  have hev : KEven IsK → ∀ (X : Type) [Group X], IsK X →
      Nonempty ((↥P ⧸ center ↥P) ≃* (X ⧸ center X)) → Odd (Nat.card ↥(center ↥P)) →
        HasEvenCover ↥N := fun hKeven _ _ _ _ hodd =>
    absurd (even_center_of_klike hmax.1.isQuasisimple hPK hKeven) (Nat.not_even_iff_odd.2 hodd)
  have hR := reach_base c hmax.1 hPK
  have hscope : ClosureScope IsK N P := Or.inr (Or.inl hPK)
  obtain ⟨Y, _, σ, hσ, hσk, hY⟩ := hPK
  have : Group.IsPerfect ↥P := hmax.1.isQuasisimple.1
  obtain ⟨e⟩ := cqEquiv_of_cover σ hσ hσk
  have hns : ¬ ∃ s ∈ S ++ Up, IsSporadic (↥P ⧸ center ↥P) s := by
    rintro ⟨s', hs', ⟨f⟩⟩
    exact c.rc.K_not_sporadic Y hY s' hs' ⟨e.symm.trans f⟩
  exact c.rc.notR H N c.hN c.hidx c.hkp ⟨L₀, hL₀, hL₀t⟩
    (known_of_maximal c.thm22.at c.rc c.ih.uHered c.hN c.hidx c.hkp hmax hR hns hlow hev hscope)

theorem twoAdic_cent_le {L P : Subgroup H} (hZ : Odd (Nat.card (center ↥L))) :
    (Nat.card ↥(centralizer (P : Set H) ⊓ L)).factorization 2 ≤
      twoAdic (autCentralizer L P) := by
  set C : Subgroup H := centralizer (P : Set H) ⊓ L with hC
  let ψ : ↥C →* ↥(autCentralizer L P) :=
    ((MulAut.conj : ↥L →* MulAut ↥L).comp (Subgroup.inclusion (inf_le_right : C ≤ L))).codRestrict
      (autCentralizer L P) (by
        intro c k hk
        have h1 : (k : H) * (c : H) = (c : H) * k :=
          (mem_centralizer_iff.1 c.2.1 k hk)
        apply Subtype.ext
        show (c : H) * k * (c : H)⁻¹ = k
        calc (c : H) * k * (c : H)⁻¹ = ((k : H) * c) * (c : H)⁻¹ := by rw [h1]
          _ = k := by group)
  have hkodd : Odd (Nat.card ψ.ker) := by
    let κ : ↥ψ.ker →* ↥(center ↥L) := MonoidHom.mk' (fun x =>
      ⟨Subgroup.inclusion (inf_le_right : C ≤ L) x.1, by
        have hx : ψ x.1 = 1 := x.2
        have h2 : (MulAut.conj (Subgroup.inclusion (inf_le_right : C ≤ L) x.1) : MulAut ↥L) = 1 :=
          congrArg Subtype.val hx
        have h3 : Subgroup.inclusion (inf_le_right : C ≤ L) x.1 ∈
            (MulAut.conj : ↥L →* MulAut ↥L).ker := h2
        rwa [ker_conj_eq_center] at h3⟩) (fun x y => rfl)
    have hκ : Function.Injective κ := fun x y h => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(center ↥L) => ((z : ↥L) : H)) h
    exact hZ.of_dvd_nat (Subgroup.card_dvd_of_injective κ hκ)
  have h1 : Nat.card ψ.ker * Nat.card ψ.range = Nat.card ↥C := Subgroup.card_ker_mul_card_range ψ
  have h2 : Nat.card ψ.range ∣ Nat.card ↥(autCentralizer L P) := Subgroup.card_subgroup_dvd_card _
  have hk0 : Nat.card ψ.ker ≠ 0 := Nat.card_pos.ne'
  have hr0 : Nat.card ψ.range ≠ 0 := Nat.card_pos.ne'
  have hA0 : Nat.card ↥(autCentralizer L P) ≠ 0 := Nat.card_pos.ne'
  rw [← h1, Nat.factorization_mul hk0 hr0]
  have h3 : (Nat.card ψ.ker).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      rcases hkodd with ⟨k, hk⟩
      omega)
  have h4 := (Nat.factorization_le_iff_dvd hr0 hA0).2 h2 2
  unfold twoAdic
  simp only [Finsupp.add_apply, h3, zero_add]
  exact h4

theorem cqCard_eq_of_isK (rc : ReachFacts IsK S Up Lo R) {P K : Subgroup H}
    (hPq : CFSG.IsQuasisimple ↥P) (hKq : CFSG.IsQuasisimple ↥K)
    (hP : IsK (↥P ⧸ CFSG.oddCore ↥P)) (hK : IsK (↥K ⧸ CFSG.oddCore ↥K)) :
    cqCard P = cqCard K := by
  have := hPq.1
  have := hKq.1
  obtain ⟨e₁⟩ := cqEquiv_of_cover (QuotientGroup.mk' (CFSG.oddCore ↥P))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact oddCore_le_center hPq)
  obtain ⟨e₂⟩ := cqEquiv_of_cover (QuotientGroup.mk' (CFSG.oddCore ↥K))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact oddCore_le_center hKq)
  obtain ⟨e⟩ := rc.K_cq _ _ hP hK
  exact Nat.card_congr (e₁.trans (e.trans e₂.symm)).toEquiv

@[expose] def TwoAdicTable (IsK : GroupClass) (S : List TauCeti.SporadicName) (H : Type) [Group H]
    [Finite H] : Prop :=
  ∀ (L P T : Subgroup H) (s : H), (∃ s' ∈ S, OddCover s' L) → T ≠ ⊥ → Sol78Link5bData P L T s →
    CFSG.IsQuasisimple ↥P → IsK (↥P ⧸ CFSG.oddCore ↥P) → twoAdic (autCentralizer L P) ≤ 2

theorem single_link_of_lt_le (c : DescCtx H N IsK S Up Lo R) {L₀ : Subgroup H} (hL₀ : InL L₀)
    (hL₀t : ∃ s ∈ S, OddCover s L₀) (htab : TwoAdicTable IsK S H) {K₁ L₁ : Subgroup H}
    (hK₁L : InL K₁) (hmax : Maximal L₁) (hlt : Lt K₁ L₁) (hKL : K₁ ≤ L₁)
    (hK : IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    (∃ s' ∈ S, OddCover s' L₁) ∧
      ∃ (T : Subgroup H) (s : H), T ≠ ⊥ ∧ Sol78Link5bData K₁ L₁ T s := by
  have hKlike : KLike IsK K₁ := klike_of_quot hK₁L.isQuasisimple hK
  have hL₁L : InL L₁ := hmax.1
  have hq₁ : CFSG.IsQuasisimple ↥L₁ := hL₁L.isQuasisimple
  have hL₁ne := inL_ne_of_fStarSimple c.hN hL₁L
  have hne : K₁ ≠ L₁ := fun h => false_of_klike_maximal c hL₀ hL₀t (h ▸ hmax) hKlike
  have hty : ∃ s' ∈ S, OddCover s' L₁ := by
    rcases desc_of_reach c hL₀ hL₀t hK₁L hKlike (ReflTransGen.single hlt) with
      ⟨π, hπ, hk⟩ | ⟨hty, -⟩
    · exact (false_of_klike_maximal c hL₀ hL₀t hmax
        (KLike.of_central_cover hKlike hq₁.1 π hπ hk)).elim
    · exact hty
  refine ⟨hty, ?_⟩
  have hRK := reach_base c hK₁L hKlike
  obtain ⟨m, L, T, s, hm, hch, h0, hT, hle'⟩ :=
    c.junction c.hkp N c.hN K₁ L₁ hK₁L hL₁L hlt hne (c.rc.not_exc _ hRK).1 (c.rc.not_exc _ hRK).2
  have hle := hle' hKL
  have hlast : L m = L₁ := hch.last
  have hleq : ∀ i, i ≤ m → L i ≤ L₁ := fun i hi => by
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h, h0]; exact hKL
    · exact hle i h hi
  have hL0 : InL (L 0) := by rw [h0]; exact hK₁L
  have hRL := reach_chain c.ih c.hUp c.rc c.hN c.hidx c.hkp hch hT hL0 hK₁L hKlike
    (by rw [h0]; exact Reached.refl hRK)
  have h5b : Sol78Link5b (L m) (L (m - 1)) (s m) := by
    rcases hch.link m hm le_rfl with h5a | h5b
    · exfalso
      have hPq : CFSG.IsQuasisimple ↥(L (m - 1)) := (hch.elem m hm le_rfl).2.2.2.isQuasisimple
      have hQq : CFSG.IsQuasisimple ↥(L m) := (hch.comp m le_rfl).2.isQuasisimple
      obtain ⟨e⟩ := h5a.2
      have hlq : L (m - 1) ≤ L m := by
        rw [hlast]
        exact hleq (m - 1) (by omega)
      have heq := eq_of_le_of_iso hlq hPq hQq ⟨e.symm⟩
      have := hch.inj (m - 1) (by omega) m le_rfl heq
      omega
    · exact h5b
  rcases Nat.lt_or_ge 1 m with hm2 | hm1
  ·
    exfalso
    have hPq : CFSG.IsQuasisimple ↥(L (m - 1)) := (hch.elem m hm le_rfl).2.2.2.isQuasisimple
    have hPL : L (m - 1) ≤ L₁ := hleq (m - 1) (by omega)
    have hK' : IsK (↥(L (m - 1)) ⧸ CFSG.oddCore ↥(L (m - 1))) :=
      chain_link5b_isK c.ih c.hUp c.rc c.hKiso c.hN c.hidx c.hkp hch hT hL0 hK₁L hKlike hm
        le_rfl h5b (hRL _ (by omega)) (by rw [hlast]; exact hty)
    have hdata : Sol78Link5bData (L (m - 1)) L₁ (T m) (s m) := by
      rw [← hlast]
      exact chain_link5bData hch hm le_rfl h5b
    have hbound := htab L₁ (L (m - 1)) (T m) (s m) hty (hT m hm le_rfl) hdata hPq hK'
    have hcq := cqCard_eq_of_isK c.rc hPq hK₁L.isQuasisimple hK' hK
    rcases hch.link (m - 1) (by omega) (by omega) with h5a' | h5b'
    ·
      obtain ⟨π, hπ, hk, hdiag⟩ := chain_link5a_diag hch (i := m - 1) (by omega) (by omega) h5a'
      obtain ⟨hTp, hLc⟩ := hch.comp (m - 1) (by omega)
      obtain ⟨hsp, hsN, hs2, hLp⟩ := hch.elem (m - 1) (by omega) (by omega)
      have hA' : IsCompIn ((L (m - 1)).map (MulAut.conj (s (m - 1))).toMonoidHom)
          (centralizer (T (m - 1) : Set H)) :=
        isCompIn_map_conj_of_mem_normalizer hLc (mem_normalizer_centralizer_of_mem_normalizer hsN)
      have hcomm := hLc.commute_of_ne hA' h5a'.1
      have hBL : L (m - 1 - 1) ≤ L₁ := hleq (m - 1 - 1) (by omega)
      have hA'C : (L (m - 1)).map (MulAut.conj (s (m - 1))).toMonoidHom ≤
          centralizer ((L (m - 1) : Subgroup H) : Set H) ⊓ L₁ := by
        rintro _ ⟨a, ha, rfl⟩
        refine ⟨mem_centralizer_iff.2 fun x hx => hcomm x hx _ ⟨a, ha, rfl⟩, ?_⟩
        have h1 : (a : H) * (s (m - 1) * (a : H) * (s (m - 1))⁻¹) ∈ L (m - 1 - 1) :=
          hdiag ⟨a, ha⟩ ▸ (π ⟨a, ha⟩).2
        have h2 : (a : H) ∈ L₁ := hPL ha
        have h3 : (a : H)⁻¹ * ((a : H) * (s (m - 1) * (a : H) * (s (m - 1))⁻¹)) ∈ L₁ :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) (hBL h1)
        simpa [MulAut.conj_apply] using h3
      have h8 : 2 ^ 3 ∣ Nat.card ↥(L (m - 1)) := by
        have hr := c.rc.rank _ hPq (hRL _ (by omega)).1
          fun _ => not_sporadic_of_isK_quot c.rc hPq hK'
        rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hr
        obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank one_lt_two (⊤ : Subgroup ↥(L (m - 1)))
        exact (pow_dvd_pow 2 hr).trans (hE ▸ Subgroup.card_subgroup_dvd_card E)
      have h8' : 2 ^ 3 ∣ Nat.card ↥(centralizer ((L (m - 1) : Subgroup H) : Set H) ⊓ L₁) := by
        refine h8.trans ?_
        rw [← Subgroup.card_map_of_injective (f := (MulAut.conj (s (m - 1))).toMonoidHom)
          (MulAut.conj (s (m - 1))).injective]
        exact Subgroup.card_dvd_of_le hA'C
      have hZ : Odd (Nat.card (center ↥L₁)) := by
        obtain ⟨s', -, -, hodd, -⟩ := hty
        exact hodd
      have hfac := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
        Nat.card_pos.ne').1 h8'
      have hcent := twoAdic_cent_le (P := L (m - 1)) hZ
      omega
    ·
      have h1 := chain_link5b_lt hch (i := m - 1) (by omega) (by omega) h5b'
      have h2 := chain_zero_le hch (m - 1 - 1) (by omega)
      rw [h0] at h2
      have h3 : cqCard K₁ ≤ cqCard (L (m - 1 - 1)) := by simpa using h2
      omega
  ·
    have hm1' : m = 1 := by omega
    subst hm1'
    refine ⟨T 1, s 1, ?_, ?_⟩
    · intro hb
      have := (hch.comp 1 le_rfl).2
      rw [hb, hlast] at this
      exact hL₁ne (c.hN.eq_of_isCompIn_bot this)
    · obtain ⟨hTp, hLc⟩ := hch.comp 1 le_rfl
      obtain ⟨hsp, hsN, hs2, hKc⟩ := hch.elem 1 le_rfl le_rfl
      obtain ⟨hincl, hincl2⟩ := hch.incl 1 le_rfl le_rfl
      simp only [Nat.sub_self, h0, hlast] at hKc hincl hincl2 h5b
      rw [hlast] at hLc
      exact ⟨hTp, hLc, hsp, hsN, hs2, hKc, ⟨hincl, hincl2⟩, h5b⟩

end CFSG.EvenSporadicStandard.Induction.Hyp
