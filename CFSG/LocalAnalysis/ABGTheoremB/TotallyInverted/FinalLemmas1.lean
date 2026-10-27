module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalInputs
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.LocalAnalysis.ABGTheoremB.Facts
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalQ

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec11

open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

theorem oddCore_map_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) : (CFSG.oddCore X).map e.toMonoidHom = CFSG.oddCore Y := by
  apply le_antisymm
  · exact le_sSup ⟨(CFSG.oddCore_normal X).map _ e.surjective,
      by rw [Subgroup.card_map_of_injective e.injective]; exact odd_card_oddCore X⟩
  · have hle : (CFSG.oddCore Y).map e.symm.toMonoidHom ≤ CFSG.oddCore X :=
      le_sSup ⟨(CFSG.oddCore_normal Y).map _ e.symm.surjective,
        by rw [Subgroup.card_map_of_injective e.symm.injective]; exact odd_card_oddCore Y⟩
    intro y hy
    exact ⟨e.symm y, hle ⟨y, hy, rfl⟩, by simp⟩

theorem oddCoreIn_conjSub (g : G) (X : Subgroup G) :
    oddCoreIn (conjSub g X) = conjSub g (oddCoreIn X) := by
  set f : G →* G := (MulAut.conj g).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj g).injective
  set e : X ≃* conjSub g X := X.equivMapOfInjective f hf
  have hcomm : (conjSub g X).subtype.comp e.toMonoidHom = f.comp X.subtype := by
    ext h
    rfl
  rw [oddCoreIn, oddCoreIn, ← oddCore_map_mulEquiv e, Subgroup.map_map, hcomm, conjSub,
    Subgroup.map_map]

theorem mem_normalizer_oddCoreIn {n : G} {X : Subgroup G}
    (hn : n ∈ Subgroup.normalizer (X : Set G)) :
    n ∈ Subgroup.normalizer ((oddCoreIn X : Subgroup G) : Set G) := by
  rw [← conjSub_eq_self_iff, ← oddCoreIn_conjSub, conjSub_eq_self_iff.mpr hn]

theorem centralizer_le_normalizer (X : Subgroup G) :
    Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  intro c hc
  apply mem_normalizer_of_conj_mem
  intro x hx
  rw [(Subgroup.mem_centralizer_iff.mp hc x hx).symm, mul_inv_cancel_right]
  exact hx

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
  intro n hn
  rw [← conjSub_eq_self_iff, conjSub_centralizer, conjSub_eq_self_iff.mpr hn]

theorem oddCoreIn_centralizer_le (X : Subgroup G) :
    oddCoreIn (Subgroup.centralizer (X : Set G)) ≤ oddCoreIn (Subgroup.normalizer (X : Set G)) :=
  le_oddCoreIn ((oddCoreIn_le _).trans (centralizer_le_normalizer X))
    (fun _ hn => mem_normalizer_oddCoreIn (normalizer_le_normalizer_centralizer X hn))
    (odd_card_oddCoreIn _)

theorem isCyclic_of_inf_centralizer {S : Subgroup G} (hS : IsPGroup 2 S) {x : G} (hx : x ∈ S)
    (hx2 : orderOf x = 2)
    (hc : IsCyclic (S ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G)) : IsCyclic S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx2; omega
  have hnt : Nontrivial S := ⟨⟨⟨x, hx⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  have hZnt := hS.center_nontrivial
  have hZp : IsPGroup 2 (Subgroup.center S) := hS.to_subgroup _
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    rcases k with _ | k
    · exfalso
      have := Finite.one_lt_card_iff_nontrivial.mpr hZnt
      rw [hk] at this
      norm_num at this
    · rw [hk, pow_succ]
      exact Dvd.intro_left _ rfl
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center S) 2 hdvd
  set z' : G := ((z : S) : G) with hz'
  have hz'2 : orderOf z' = 2 := by
    rw [hz', Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hz'c : ∀ s ∈ S, z' * s = s * z' := by
    intro s hs
    have := Subgroup.mem_center_iff.mp z.2 ⟨s, hs⟩
    exact (congrArg Subtype.val this).symm
  have hxz : x = z' := by
    by_contra hne
    set D : Subgroup G := S ⊓ Subgroup.centralizer ({x} : Set G) with hD
    have hxD : x ∈ D := ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hzD : z' ∈ D :=
      ⟨(z : S).2, Subgroup.mem_centralizer_singleton_iff.mpr (hz'c x hx)⟩
    have : Fintype D := Fintype.ofFinite D
    have hle := IsCyclic.card_pow_eq_one_le (α := D) (n := 2) (by norm_num)
    have hsub : ({1, ⟨x, hxD⟩, ⟨z', hzD⟩} : Finset D) ⊆
        Finset.univ.filter (fun a : D => a ^ 2 = 1) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases ha with rfl | rfl | rfl
      · exact one_pow 2
      · exact Subtype.ext (by simp [← hx2])
      · exact Subtype.ext (by simp [← hz'2])
    have hcard : ({1, ⟨x, hxD⟩, ⟨z', hzD⟩} : Finset D).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · intro h
        exact hne (congrArg Subtype.val h)
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun h => hx1 (congrArg Subtype.val h).symm, fun h => ?_⟩
        have := congrArg Subtype.val h
        exact (fun h1 : z' = 1 => by rw [h1, orderOf_one] at hz'2; omega) this.symm
    have := (Finset.card_le_card hsub).trans hle
    omega
  have hSx : S ⊓ Subgroup.centralizer ({x} : Set G) = S := by
    refine inf_eq_left.mpr fun s hs => ?_
    rw [Subgroup.mem_centralizer_singleton_iff, hxz]
    exact (hz'c s hs).symm
  rw [hSx] at hc
  exact hc

theorem le_oddCoreIn_of_cyclic_sylow {H X : Subgroup G} (S : Sylow 2 H) (hS : IsCyclic S)
    (hXH : X ≤ H) (hX : Odd (Nat.card X)) : X ≤ oddCoreIn H := by
  obtain ⟨-, -, -, ⟨hKn, hKodd, hKind, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hS
  set K := CFSG.pPrimeCore 2 H
  have hKO : K ≤ CFSG.oddCore H := le_sSup ⟨hKn, hKodd⟩
  intro u hu
  have hmem : (⟨u, hXH hu⟩ : H) ∈ K := by
    rw [← QuotientGroup.eq_one_iff]
    set v : H ⧸ K := ((⟨u, hXH hu⟩ : H) : H ⧸ K)
    have h1 : orderOf v ∣ orderOf u := by
      have := orderOf_map_dvd (QuotientGroup.mk' K) (⟨u, hXH hu⟩ : H)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf v ∣ Nat.card S := by
      rw [← hKind, Subgroup.index_eq_card]
      exact orderOf_dvd_natCard v
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    rw [hk] at h2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    have hodd : Odd (orderOf v) := (odd_orderOf_of_mem hX hu).of_dvd_nat h1
    rcases j with _ | j
    · exact orderOf_eq_one_iff.mp (by simpa using hj)
    · rw [hj, pow_succ] at hodd
      exact absurd hodd (by simp)
  exact ⟨⟨u, hXH hu⟩, hKO hmem, rfl⟩

theorem le_oddCore_normalizer_of_cyclic (hσ : σ.IsValid) {Q X : Subgroup G} (hQN : Q ≤ σ.N)
    (hcyc : ∀ Y : Subgroup G, Y ≤ σ.N → IsPGroup 2 Y →
      Y ≤ Subgroup.centralizer (Q : Set G) → IsCyclic Y)
    (hX : X ≤ Subgroup.centralizer (Q : Set G)) (hXodd : Odd (Nat.card X)) :
    X ≤ oddCoreIn (Subgroup.normalizer (Q : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H₀ : Subgroup G := Subgroup.centralizer (Q : Set G) with hH₀
  have hxH : σ.x ∈ H₀ := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hQN hq))
  have hP : IsPGroup 2 (Subgroup.zpowers (⟨σ.x, hxH⟩ : H₀)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hσ.x_order, pow_one]
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  set S' : Subgroup G := (S : Subgroup H₀).map H₀.subtype with hS'
  have hS'p : IsPGroup 2 S' := S.isPGroup'.map _
  have hxS' : σ.x ∈ S' := ⟨⟨σ.x, hxH⟩, hPS (Subgroup.mem_zpowers _), rfl⟩
  have hS'H : S' ≤ H₀ := Subgroup.map_subtype_le _
  have hcS' : IsCyclic S' := by
    apply isCyclic_of_inf_centralizer hS'p hxS' hσ.x_order
    exact hcyc _ inf_le_right (hS'p.to_le inf_le_left) (inf_le_left.trans hS'H)
  have hcS : IsCyclic S := by
    have e : (S : Subgroup H₀) ≃* S' :=
      (S : Subgroup H₀).equivMapOfInjective H₀.subtype H₀.subtype_injective
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  exact (le_oddCoreIn_of_cyclic_sylow S hcS hX hXodd).trans (oddCoreIn_centralizer_le Q)

theorem lemma11_1 (hσ : σ.IsValid) (Δ : Data σ r) (homni : Omnibus Δ) {H A B : Subgroup G}
    (hCH : σ.C ≤ H) (hAH : A ≤ H) (hBH : B ≤ oddCoreIn H) (hA : IsPGroup r A)
    (hB : IsPGroup r B) (hCA : σ.C ≤ Subgroup.normalizer (A : Set G))
    (hCB : σ.C ≤ Subgroup.normalizer (B : Set G)) : IsPGroup r (A ⊔ B : Subgroup G) := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  have hTC := σ.T_le_C hσ
  have hAmem : A ∈ signalizersPerm H σ.T σ.C r :=
    ⟨⟨hAH, hA, hTC.trans hCA, inf_T_eq_bot hσ Δ.prime Δ.ne_two hA⟩,
      mul_comm_of_le_normalizer hCA⟩
  obtain ⟨U, hU, hAU⟩ := exists_le_mem_maximals hAmem
  obtain ⟨R₀, hR₀, hR₀U⟩ := (homni H hCH U hU).part_ii_b
  have hUp : IsPGroup r U := hU.1.1.2.1
  have hS₀ : IsSylowOf r (U ⊓ oddCoreIn H) (oddCoreIn H) := by
    rw [hR₀.eq_of_le (le_inf hR₀U hR₀.le) inf_le_right (hUp.to_le inf_le_left)]
    exact hR₀
  have hTO : σ.T ≤ Subgroup.normalizer ((oddCoreIn H : Subgroup G) : Set G) :=
    (hTC.trans hCH).trans (le_normalizer_oddCoreIn H)
  have hTS : σ.T ≤ Subgroup.normalizer ((U ⊓ oddCoreIn H : Subgroup G) : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_inf ⟨hU.1.1.2.2.1 ht, hTO ht⟩
  obtain ⟨c, hc, hBc⟩ := exists_le_conjSub_of_coprime (card_T hσ) (odd_card_oddCoreIn H) hTO hS₀
    hBH hB hTS (hTC.trans hCB)
  have hcC : c ∈ σ.C := hc.2
  have hBU : B ≤ U := by
    have h1 := conjSub_mono (g := c⁻¹) hBc
    rw [conjSub_inv_conjSub, conjSub_eq_self_iff.mpr (hCB (σ.C.inv_mem hcC))] at h1
    exact h1.trans inf_le_left
  exact hUp.to_le (sup_le hAU hBU)

theorem J_le_centralizer_Ps (Δ : Data σ r) :
    Δ.J ≤ Subgroup.centralizer (σ.Ps r 0 : Set G) :=
  fun _ hj => Subgroup.centralizer_le (Ps_zero_le_ON Δ) (Δ.J_centralizes hj)

theorem Q_zero_le_J (Δ : Data σ r) : Δ.Q 0 ≤ Δ.J := by
  simpa [conjSub_one] using Q_le_J_conj Δ 0

theorem Qs_zero_le_J (Δ : Data σ r) : Δ.Qs 0 ≤ Δ.J := by
  simpa [conjSub_one] using Qs_le_J_conj Δ 0

theorem Ps_le_centralizer_of_le (Δ : Data σ r) (i : Fin 3) {X : Subgroup G}
    (hX : X ≤ σ.Ps r i) : σ.Ps r i ≤ Subgroup.centralizer (X : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact Δ.P_abelian i h (hX hh) g hg

theorem covers_of_J_le (hσ : σ.IsValid) (Δ : Data σ r) {H : Subgroup G} (hJH : Δ.J ≤ H) :
    (σ.L₀ : Set G) ⊆ (H : Set G) * (σ.ON : Set G) := by
  intro l hl
  rw [SetLike.mem_coe, Δ.L₀_eq] at hl
  obtain ⟨j, hj, o, ho, rfl⟩ :=
    (mem_sup_iff_of_le_normalizer ((J_le_N hσ Δ).trans σ.N_le_normalizer_ON)).mp hl
  exact Set.mul_mem_mul (hJH hj) ho

theorem mem_oddCoreIn_of_inverted_of_J_le (hσ : σ.IsValid) (hF : σ.ChapterIIFacts)
    (Δ : Data σ r) {H : Subgroup G} (hCH : σ.C ≤ H) (hO : oddCoreIn H ≠ ⊥) (hJH : Δ.J ≤ H)
    {u : G} (hu : u ∈ H) (huo : Odd (orderOf u)) (hinv : σ.x * u * σ.x⁻¹ = u⁻¹) :
    u ∈ oddCoreIn H :=
  mem_oddCoreIn_of_inverted (hCH (σ.T_le_C hσ σ.x_mem_T))
    (hF.cover_qgroup H ((σ.T_le_C hσ).trans hCH) hO (covers_of_J_le hσ Δ hJH)).2 hu huo hinv

theorem lemma11_2 (hσ : σ.IsValid) (hF : σ.ChapterIIFacts) (Δ : Data σ r) (homni : Omnibus Δ)
    {A B : Subgroup G} (hA : A = R Δ 0 ∨ A = Rs Δ 0) (hB : IsPGroup r B)
    (hCB : σ.C ≤ Subgroup.normalizer (B : Set G))
    (hinv : ∀ u ∈ B, σ.x * u * σ.x⁻¹ = u⁻¹)
    (hne : σ.Ps r 0 ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥) :
    IsPGroup r (A ⊔ B : Subgroup G) := by
  set R' : Subgroup G := σ.Ps r 0 ⊓ Subgroup.centralizer (B : Set G) with hR'
  set H : Subgroup G := Subgroup.normalizer (R' : Set G) with hH
  have hR'P : R' ≤ σ.Ps r 0 := inf_le_left
  have hCH : σ.C ≤ H := fun c hc => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨C_le_normalizer_Ps r 0 hc, normalizer_le_normalizer_centralizer B (hCB hc)⟩
  have hcentH : Subgroup.centralizer (R' : Set G) ≤ H := centralizer_le_normalizer R'
  have hJH : Δ.J ≤ H := fun j hj =>
    hcentH (Subgroup.centralizer_le hR'P (J_le_centralizer_Ps Δ hj))
  have hPH : σ.Ps r 0 ≤ H := (Ps_le_centralizer_of_le Δ 0 hR'P).trans hcentH
  have hAH : A ≤ H := by
    rcases hA with rfl | rfl
    · exact sup_le ((Q_zero_le_J Δ).trans hJH) hPH
    · exact sup_le ((Qs_zero_le_J Δ).trans hJH) hPH
  have hBcent : B ≤ Subgroup.centralizer (R' : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp hg.2 b hb).symm
  have hBH : B ≤ H := hBcent.trans hcentH
  have hR'O : R' ≤ oddCoreIn H := le_oddCoreIn Subgroup.le_normalizer le_rfl
    (odd_card_of_isPGroup Δ.prime Δ.ne_two ((isPGroup_Ps 0).to_le hR'P))
  have hO : oddCoreIn H ≠ ⊥ := fun h => hne (eq_bot_iff.mpr (h ▸ hR'O))
  have hBO : B ≤ oddCoreIn H := fun u hu =>
    mem_oddCoreIn_of_inverted_of_J_le hσ hF Δ hCH hO hJH (hBH hu)
      (odd_orderOf_of_mem (odd_card_of_isPGroup Δ.prime Δ.ne_two hB) hu) (hinv u hu)
  have hAp : IsPGroup r A := by
    rcases hA with rfl | rfl
    · exact isPGroup_R Δ hσ 0
    · exact isPGroup_Rs Δ hσ 0
  have hCA : σ.C ≤ Subgroup.normalizer (A : Set G) := by
    rcases hA with rfl | rfl
    · exact C_le_normalizer_R Δ 0
    · exact C_le_normalizer_Rs Δ 0
  exact lemma11_1 hσ Δ homni hCH hAH hBO hAp hB hCA hCB

omit [Finite G] in
theorem conjSub_inf_centralizer (g : G) (P X : Subgroup G) :
    conjSub g (P ⊓ Subgroup.centralizer (X : Set G)) =
      conjSub g P ⊓ Subgroup.centralizer (conjSub g X : Set G) := by
  rw [conjSub_inf, conjSub_centralizer]

theorem pGroupR_of_centralizer_Ps0_R2 (hσ : σ.IsValid) (hF : σ.ChapterIIFacts)
    (Δ : Data σ r) (homni : Omnibus Δ)
    (h : σ.Ps r 0 ⊓ Subgroup.centralizer (R Δ 2 : Set G) ≠ ⊥) : PGroupR Δ :=
  lemma11_2 hσ hF Δ homni (Or.inl rfl) (isPGroup_R Δ hσ 2) (C_le_normalizer_R Δ 2)
    (fun _ hu => R_inverted Δ hσ (j := 0) (by decide) hu) h

theorem pGroupR_of_centralizer_Ps0_R1 (hσ : σ.IsValid) (hF : σ.ChapterIIFacts)
    (Δ : Data σ r) (homni : Omnibus Δ)
    (h : σ.Ps r 0 ⊓ Subgroup.centralizer (R Δ 1 : Set G) ≠ ⊥) : PGroupR Δ :=
  pGroupR_of_R01 Δ (lemma11_2 hσ hF Δ homni (Or.inl rfl) (isPGroup_R Δ hσ 1)
    (C_le_normalizer_R Δ 1) (fun _ hu => R_inverted Δ hσ (j := 0) (by decide) hu) h)

theorem pGroupR_of_centralizer_Ps0_Rs1 (hσ : σ.IsValid) (hF : σ.ChapterIIFacts)
    (Δ : Data σ r) (homni : Omnibus Δ)
    (h : σ.Ps r 0 ⊓ Subgroup.centralizer (Rs Δ 1 : Set G) ≠ ⊥) : PGroupR Δ :=
  pGroupR_of_Rs01 hσ Δ (lemma11_2 hσ hF Δ homni (Or.inr rfl) (isPGroup_Rs Δ hσ 1)
    (C_le_normalizer_Rs Δ 1) (fun _ hu => Rs_inverted Δ hσ (j := 0) (by decide) hu) h)

theorem pGroupR_of_centralizer_Ps1_R0 (hσ : σ.IsValid) (hF : σ.ChapterIIFacts)
    (Δ : Data σ r) (homni : Omnibus Δ)
    (h : σ.Ps r 1 ⊓ Subgroup.centralizer (R Δ 0 : Set G) ≠ ⊥) : PGroupR Δ := by
  apply pGroupR_of_centralizer_Ps0_R2 hσ hF Δ homni
  have h' : conjSub (Δ.a ^ ((2 : Fin 3) : ℕ))
      (σ.Ps r 1 ⊓ Subgroup.centralizer (R Δ 0 : Set G)) ≠ ⊥ := by
    rwa [Ne, conjSub_eq_bot_iff]
  rwa [conjSub_inf_centralizer, conjSub_a_pow_Ps, conjSub_a_pow_R] at h'

theorem pGroupR_of_centralizer_Ps2_R0 (hσ : σ.IsValid) (hF : σ.ChapterIIFacts)
    (Δ : Data σ r) (homni : Omnibus Δ)
    (h : σ.Ps r 2 ⊓ Subgroup.centralizer (R Δ 0 : Set G) ≠ ⊥) : PGroupR Δ := by
  apply pGroupR_of_centralizer_Ps0_R1 hσ hF Δ homni
  have h' : conjSub (Δ.a ^ ((1 : Fin 3) : ℕ))
      (σ.Ps r 2 ⊓ Subgroup.centralizer (R Δ 0 : Set G)) ≠ ⊥ := by
    rwa [Ne, conjSub_eq_bot_iff]
  rwa [conjSub_inf_centralizer, conjSub_a_pow_Ps, conjSub_a_pow_R] at h'

section Lemma5

variable (Δ : Data σ r) (hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q)
include hδq

theorem R_le_centralizer_Q (hσ : σ.IsValid) (i : Fin 3) :
    R Δ i ≤ Subgroup.centralizer (Δ.Q i : Set G) := by
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Q_abelian Δ hδq hσ i h hh g hg
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_iff.mp (Q_le_centralizer_Ps Δ hδq i hh) g hg).symm

theorem Rs_le_centralizer_Qs (hσ : σ.IsValid) (i : Fin 3) :
    Rs Δ i ≤ Subgroup.centralizer (Δ.Qs i : Set G) := by
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Qs_abelian Δ hδq hσ i h hh g hg
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_iff.mp (Qs_le_centralizer_Ps Δ hδq i hh) g hg).symm

theorem R_le_oddCore_normalizer_Q (hσ : σ.IsValid) (hI : ABG_II_4_4 Δ) (i : Fin 3) :
    R Δ i ≤ oddCoreIn (Subgroup.normalizer (Δ.Q i : Set G)) := by
  have h0 : R Δ 0 ≤ oddCoreIn (Subgroup.normalizer (Δ.Q 0 : Set G)) :=
    le_oddCore_normalizer_of_cyclic hσ (Q_le_Ns Δ hσ 0)
      (fun Y hYN hY hYQ => hI hδq Y hYN hY (Or.inl hYQ)) (R_le_centralizer_Q Δ hδq hσ 0)
      (odd_card_R Δ hσ 0)
  have h := conjSub_mono (g := Δ.a ^ (i : ℕ)) h0
  rwa [← oddCoreIn_conjSub, ← normalizer_conjSub, conjSub_a_pow_R, conjSub_a_pow_Q,
    zero_add] at h

theorem Rs_le_oddCore_normalizer_Qs (hσ : σ.IsValid) (hI : ABG_II_4_4 Δ) (i : Fin 3) :
    Rs Δ i ≤ oddCoreIn (Subgroup.normalizer (Δ.Qs i : Set G)) := by
  have h0 : Rs Δ 0 ≤ oddCoreIn (Subgroup.normalizer (Δ.Qs 0 : Set G)) :=
    le_oddCore_normalizer_of_cyclic hσ (Qs_le_Ns Δ hσ 0)
      (fun Y hYN hY hYQ => hI hδq Y hYN hY (Or.inr hYQ)) (Rs_le_centralizer_Qs Δ hδq hσ 0)
      (odd_card_Rs Δ hσ 0)
  have h := conjSub_mono (g := Δ.a ^ (i : ℕ)) h0
  rwa [← oddCoreIn_conjSub, ← normalizer_conjSub, conjSub_a_pow_Rs, conjSub_a_pow_Qs,
    zero_add] at h

end Lemma5

theorem eq_of_le_sup_of_irred {C A P W X : Subgroup G}
    (hAP : A ≤ Subgroup.centralizer (P : Set G))
    (hCA : C ≤ Subgroup.normalizer (A : Set G)) (hCP : C ≤ Subgroup.normalizer (P : Set G))
    (hirr : ∀ Y : Subgroup G, Y ≤ A → C ≤ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = A)
    (hWC : W ≤ C) (hWP : W ≤ Subgroup.centralizer (P : Set G))
    (hWA : ¬ W ≤ Subgroup.centralizer (A : Set G)) (hXAP : X ≤ A ⊔ P)
    (hCX : C ≤ Subgroup.normalizer (X : Set G)) (hXP : X ⊓ P = ⊥) (hX1 : X ≠ ⊥) : X = A := by
  have hAPn : A ≤ Subgroup.normalizer (P : Set G) := hAP.trans (centralizer_le_normalizer P)
  have hsupn : A ⊔ P ≤ Subgroup.normalizer (P : Set G) := sup_le hAPn Subgroup.le_normalizer
  have hXPn : X ≤ Subgroup.normalizer (P : Set G) := hXAP.trans hsupn
  have hA_le : A ≤ X ⊔ P := by
    have hCZ : C ≤ Subgroup.normalizer (((X ⊔ P) ⊓ A : Subgroup G) : Set G) :=
      fun c hc => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨mem_normalizer_sup (hCX hc) (hCP hc), hCA hc⟩
    rcases hirr _ inf_le_right hCZ with h | h
    · exfalso
      apply hX1
      have hD := inf_sup_eq_of_le (M := X ⊔ P) hAPn le_sup_right
      rw [h, bot_sup_eq, inf_eq_left.mpr (sup_le hXAP le_sup_right)] at hD
      rw [eq_bot_iff, ← hXP]
      exact le_inf le_rfl (le_sup_left.trans hD.le)
    · rw [← h]
      exact inf_le_left
  have hcomm : ∀ w ∈ W, ∀ u ∈ X, w * u * w⁻¹ * u⁻¹ ∈ X ⊓ A := by
    intro w hw u hu
    obtain ⟨a, ha, p, hp, rfl⟩ := (mem_sup_iff_of_le_normalizer hAPn).mp (hXAP hu)
    have hwp : w * p * w⁻¹ = p := by
      rw [← (Subgroup.mem_centralizer_iff.mp (hWP hw) p hp), mul_inv_cancel_right]
    refine ⟨?_, ?_⟩
    · have h1 : w * (a * p) * w⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hCX (hWC hw)) _).mp hu
      exact X.mul_mem h1 (X.inv_mem hu)
    · have h2 : w * a * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hCA (hWC hw)) _).mp ha
      have e : w * (a * p) * w⁻¹ * (a * p)⁻¹ = (w * a * w⁻¹) * a⁻¹ := by
        calc w * (a * p) * w⁻¹ * (a * p)⁻¹ = (w * a * w⁻¹) * (w * p * w⁻¹) * p⁻¹ * a⁻¹ := by
              group
          _ = (w * a * w⁻¹) * a⁻¹ := by rw [hwp]; group
      rw [e]
      exact A.mul_mem h2 (A.inv_mem ha)
  have hCXA : C ≤ Subgroup.normalizer ((X ⊓ A : Subgroup G) : Set G) :=
    fun c hc => Subgroup.inf_normalizer_le_normalizer_inf ⟨hCX hc, hCA hc⟩
  rcases hirr _ inf_le_right hCXA with h | h
  · exfalso
    apply hWA
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨u, hu, p, hp, rfl⟩ := (mem_sup_iff_of_le_normalizer hXPn).mp (hA_le ha)
    have hwu : w * u * w⁻¹ * u⁻¹ = 1 := by
      have := hcomm w hw u hu
      rw [h] at this
      exact this
    have hwu' : w * u = u * w := by
      calc w * u = (w * u * w⁻¹ * u⁻¹) * u * w := by group
        _ = u * w := by rw [hwu, one_mul]
    have hwp : w * p = p * w := (Subgroup.mem_centralizer_iff.mp (hWP hw) p hp).symm
    calc u * p * w = u * (p * w) := by group
      _ = u * (w * p) := by rw [hwp]
      _ = w * (u * p) := by rw [← mul_assoc, ← hwu', mul_assoc]
  · have hAX : A ≤ X := h ▸ inf_le_left
    apply le_antisymm _ hAX
    intro u hu
    obtain ⟨a, ha, p, hp, rfl⟩ := (mem_sup_iff_of_le_normalizer hAPn).mp (hXAP hu)
    have hpX : p ∈ X := by
      have := X.mul_mem (X.inv_mem (hAX ha)) hu
      rwa [inv_mul_cancel_left] at this
    have hp1 : p = 1 := by
      have : p ∈ X ⊓ P := ⟨hpX, hp⟩
      rw [hXP] at this
      exact this
    rw [hp1, mul_one]
    exact ha

section Complement

variable (Δ : Data σ r) (hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q)
include hδq

omit hδq in
theorem J_conj_le_centralizer_Ps (i : Fin 3) :
    conjSub (Δ.a ^ (i : ℕ)) Δ.J ≤ Subgroup.centralizer (σ.Ps r i : Set G) := by
  have h := conjSub_mono (g := Δ.a ^ (i : ℕ)) (J_le_centralizer_Ps Δ)
  rwa [conjSub_centralizer, conjSub_a_pow_Ps, zero_add] at h

theorem C_inf_J_not_le_centralizer_Q (hI : ABG_II_4_10_iii Δ) (i : Fin 3) :
    ¬ σ.C ⊓ conjSub (Δ.a ^ (i : ℕ)) Δ.J ≤ Subgroup.centralizer (Δ.Q i : Set G) := by
  intro h
  apply (hI hδq).1
  have hQ : Δ.Q i = conjSub (Δ.a ^ (i : ℕ)) (Δ.Q 0) := by rw [conjSub_a_pow_Q, zero_add]
  rw [← conjSub_a_pow_C Δ (i : ℕ), hQ, ← conjSub_centralizer, ← conjSub_inf,
    conjSub_le_conjSub_iff] at h
  exact h

theorem C_inf_J_not_le_centralizer_Qs (hI : ABG_II_4_10_iii Δ) (i : Fin 3) :
    ¬ σ.C ⊓ conjSub (Δ.a ^ (i : ℕ)) Δ.J ≤ Subgroup.centralizer (Δ.Qs i : Set G) := by
  intro h
  apply (hI hδq).2
  have hQ : Δ.Qs i = conjSub (Δ.a ^ (i : ℕ)) (Δ.Qs 0) := by rw [conjSub_a_pow_Qs, zero_add]
  rw [← conjSub_a_pow_C Δ (i : ℕ), hQ, ← conjSub_centralizer, ← conjSub_inf,
    conjSub_le_conjSub_iff] at h
  exact h

theorem eq_Q_of_le_R (hI : ABG_II_4_10_iii Δ) (i : Fin 3) {X : Subgroup G} (hXR : X ≤ R Δ i)
    (hCX : σ.C ≤ Subgroup.normalizer (X : Set G)) (hXP : X ⊓ σ.Ps r i = ⊥) (hX1 : X ≠ ⊥) :
    X = Δ.Q i :=
  eq_of_le_sup_of_irred (Q_le_centralizer_Ps Δ hδq i) (C_le_normalizer_Q Δ i)
    (C_le_normalizer_Ps r i) (fun _ hY hCY => Q_irred Δ hδq i hY hCY) inf_le_left
    (inf_le_right.trans (J_conj_le_centralizer_Ps Δ i))
    (C_inf_J_not_le_centralizer_Q Δ hδq hI i) hXR hCX hXP hX1

theorem eq_Qs_of_le_Rs (hI : ABG_II_4_10_iii Δ) (i : Fin 3) {X : Subgroup G}
    (hXR : X ≤ Rs Δ i) (hCX : σ.C ≤ Subgroup.normalizer (X : Set G))
    (hXP : X ⊓ σ.Ps r i = ⊥) (hX1 : X ≠ ⊥) : X = Δ.Qs i :=
  eq_of_le_sup_of_irred (Qs_le_centralizer_Ps Δ hδq i) (C_le_normalizer_Qs Δ i)
    (C_le_normalizer_Ps r i) (fun _ hY hCY => Qs_irred Δ hδq i hY hCY) inf_le_left
    (inf_le_right.trans (J_conj_le_centralizer_Ps Δ i))
    (C_inf_J_not_le_centralizer_Qs Δ hδq hI i) hXR hCX hXP hX1

end Complement

end CFSG.ABGTheoremB.TotallyInverted.Sec11
