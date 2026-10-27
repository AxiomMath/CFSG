module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma36TC

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Subgroup

section Generic

variable {G : Type*} [Group G]

theorem le_oddCoreIn_of_odd {H K : Subgroup G} (hKH : K ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (K : Set G)) (hodd : Odd (Nat.card K)) :
    K ≤ oddCoreIn H := by
  have hnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hnorm
  have hodd' : Odd (Nat.card (K.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
  have hle : K.subgroupOf H ≤ fusionOddCore H := le_sSup ⟨hnormal, hodd'⟩
  intro k hk
  exact ⟨⟨k, hKH hk⟩, hle hk, rfl⟩

variable [Finite G]

theorem le_of_cyclic_sylow_of_oddCoreIn_eq_bot {G₂ B P : Subgroup G} (hBG : B ≤ G₂)
    (hBn : G₂ ≤ Subgroup.normalizer (B : Set G)) (hP : IsSylowTwoOf P B) (hcyc : IsCyclic ↥P)
    (hodd : oddCoreIn G₂ = ⊥) : B ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPB : P ≤ B := hP.le
  have hP2 : IsPGroup 2 (P.subgroupOf B) :=
    hP.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hPB).symm
  let P' : Sylow 2 ↥B := hP2.toSylow hP.2.2
  have hP'coe : (P' : Subgroup ↥B) = P.subgroupOf B := rfl
  have hcyc' : IsCyclic ↥(P' : Subgroup ↥B) := by
    rw [hP'coe]
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hPB).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPB).symm.surjective
  obtain ⟨N, hNn, hNc⟩ :=
    exists_normal_isComplement'_of_isCyclic_sylow (fun q hq _ => hq.two_le) P' hcyc'
  have hcardP : Nat.card ↥P = twoPart B := hP.card_eq
  have hcardP' : Nat.card ↥(P' : Subgroup ↥B) = twoPart B := by
    rw [hP'coe, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPB).toEquiv]
    exact hcardP
  have hmul : Nat.card ↥N * twoPart B = Nat.card ↥B := by
    rw [← hcardP']; exact hNc.card_mul_card
  obtain ⟨a, ha⟩ : ∃ a, a = (Nat.card ↥B).factorization 2 := ⟨_, rfl⟩
  have hmul' : Nat.card ↥N * 2 ^ a = Nat.card ↥B := by
    rw [ha]; exact hmul
  have hNodd : Odd (Nat.card ↥N) := by
    have h1 := congrArg (fun m => m.factorization 2) hmul'
    rw [Nat.factorization_mul Nat.card_pos.ne' (by positivity)] at h1
    simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same] at h1
    have h2 : (Nat.card ↥N).factorization 2 = 0 := by omega
    have h3 : ¬ 2 ∣ Nat.card ↥N := by
      intro hd
      have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp hd
      omega
    exact Nat.odd_iff.mpr (by omega)
  have hindex : N.index = twoPart B := by
    rw [← hcardP']; exact (hNc.symm).index_eq_card
  have hoddmem : ∀ b : ↥B, Odd (orderOf (b : G)) → b ∈ N := by
    intro b hb
    rw [Subgroup.orderOf_coe] at hb
    have hq : Nat.card (↥B ⧸ N) = twoPart B := by rw [← Subgroup.index_eq_card]; exact hindex
    have h1 : orderOf ((QuotientGroup.mk' N) b) ∣ twoPart B := by
      rw [← hq]; exact orderOf_dvd_natCard _
    have h2 : orderOf ((QuotientGroup.mk' N) b) ∣ orderOf b := orderOf_map_dvd _ _
    have hcop : Nat.Coprime (twoPart B) (orderOf b) := by
      unfold twoPart
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hb)
    have h3 : orderOf ((QuotientGroup.mk' N) b) = 1 :=
      Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
    have h4 : (QuotientGroup.mk' N) b = 1 := orderOf_eq_one_iff.mp h3
    exact (QuotientGroup.eq_one_iff b).mp h4
  let Nb : Subgroup G := N.map B.subtype
  have hNbB : Nb ≤ B := Subgroup.map_subtype_le N
  have hcardNb : Nat.card ↥Nb = Nat.card ↥N :=
    Subgroup.card_map_of_injective B.subtype_injective
  have hNbodd : Odd (Nat.card ↥Nb) := by rw [hcardNb]; exact hNodd
  have hmemNb : ∀ g : G, g ∈ Nb ↔ g ∈ B ∧ Odd (orderOf g) := by
    intro g
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨n.2, ?_⟩
      show Odd (orderOf (n : G))
      rw [Subgroup.orderOf_coe, ← Subgroup.orderOf_mk n hn]
      exact Odd.of_dvd_nat hNodd (orderOf_dvd_natCard _)
    · rintro ⟨hgB, hgodd⟩
      exact ⟨⟨g, hgB⟩, hoddmem ⟨g, hgB⟩ hgodd, rfl⟩
  have key : ∀ g ∈ G₂, ∀ y : G, y ∈ Nb → g * y * g⁻¹ ∈ Nb := by
    intro g hg y hy
    obtain ⟨hyB, hyo⟩ := (hmemNb y).mp hy
    refine (hmemNb _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hBn hg) y).mp hyB, ?_⟩
    have : orderOf (g * y * g⁻¹) = orderOf y := by
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
      simpa [MulAut.conj_apply] using this
    rw [this]; exact hyo
  have hNbnorm : G₂ ≤ Subgroup.normalizer (Nb : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key g hg y, fun h => ?_⟩
    have := key g⁻¹ (G₂.inv_mem hg) _ h
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at this
  have hle := le_oddCoreIn_of_odd (hNbB.trans hBG) hNbnorm hNbodd
  rw [hodd, le_bot_iff] at hle
  have hcard1 : Nat.card ↥N = 1 := by
    rw [← hcardNb, hle, Subgroup.card_bot]
  have hBP : Nat.card ↥B ≤ Nat.card ↥P := by
    rw [← hmul, hcard1, one_mul, hcardP]
  exact (Subgroup.eq_of_le_of_card_ge hPB hBP).symm.le

theorem factorization_two_1440 : (1440 : ℕ).factorization 2 = 5 := by
  have : (1440 : ℕ) = 2 ^ 5 * 45 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 45)]

theorem twoPart_eq_of_surjective {G₂ B : Subgroup G} {A : Type*} [Group A] (ρ : ↥G₂ →* A)
    (hρ : Function.Surjective ρ) (hker : ρ.ker = B.subgroupOf G₂) (hBG : B ≤ G₂)
    (hA : Nat.card A = 1440) : twoPart G₂ = twoPart B * 32 := by
  have h1 := ρ.ker.card_mul_index
  rw [Subgroup.index_ker, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBG).toEquiv] at h1
  have h2 : Nat.card ρ.range = 1440 := by
    rw [MonoidHom.range_eq_top.mpr hρ, Subgroup.card_top, hA]
  rw [h2] at h1
  unfold twoPart
  rw [← h1, Nat.factorization_mul Nat.card_pos.ne' (by norm_num)]
  simp only [Finsupp.add_apply, factorization_two_1440, pow_add]
  norm_num

end Generic

section Config

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s x z₁ z₂ : G} {K : Subgroup G}

theorem baum_le_normalizer_blockU (hcs : ConstrainedSetting G T M H S L) (h3 : IsAltType L 3) :
    baum S ≤ normalizer (blockU L : Set G) := fun _ hg =>
  C1.mem_normalizer_blockU (((C56.baumann_A3_cs hcs h3).2).1 hg)

theorem A3A3K.relIndex_baum_sOne (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hK : A3A3K T M H S L s x z₁ z₂ K) : (baum S).relIndex (sOne S x) = 2 := by
  have hB := basic31 hD h27_1 hK.toA3A3
  have hRS₁ : baum S ≤ sOne S x := le_sup_left
  have h1 : Nat.card (sOne S x) = Nat.card (baum S) * (baum S).relIndex (sOne S x) :=
    C5.card_eq_card_mul_relIndex hRS₁
  have h2 : Nat.card T = Nat.card (sOne S x) * (sOne S x).relIndex T :=
    C5.card_eq_card_mul_relIndex hK.toA3A3x.sOne_le_T
  have hm := hK.toA3A3x.relIndex_sOne hD h27_1
  have hpos : 0 < Nat.card (baum S) := Nat.card_pos
  have h3 : Nat.card (baum S) * ((baum S).relIndex (sOne S x) * 2) = Nat.card (baum S) * 4 := by
    calc Nat.card (baum S) * ((baum S).relIndex (sOne S x) * 2) = Nat.card T := by
          rw [h2, h1, hm]; ring
      _ = Nat.card (baum S) * 4 := by rw [hB.card_T]; ring
  have h4 := Nat.eq_of_mul_eq_mul_left hpos h3
  omega

theorem A3A3K.sOne_inf_centralizer_le (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hK : A3A3K T M H S L s x z₁ z₂ K) :
    sOne S x ⊓ Subgroup.centralizer (K : Set G) ≤ baum S := by
  rintro g ⟨hgS₁, hgC⟩
  by_contra hgR
  have hcs := hK.cs
  have hidx := hK.relIndex_baum_sOne hD h27_1
  have hxS₁ : x ∈ sOne S x := mem_sup_right (Subgroup.mem_zpowers x)
  have hxR : x ∉ baum S := fun h => hK.x_not_mem ((inf_le_left : baum S ≤ S) h)
  have hr : x⁻¹ * g ∈ baum S :=
    (mem_or_inv_mul_mem_of_relIndex_two hidx hxS₁ hxR hgS₁).resolve_left hgR
  obtain ⟨r, hrR, hgr⟩ : ∃ r ∈ baum S, g = x * r := ⟨x⁻¹ * g, hr, by group⟩
  have hUnorm := baum_le_normalizer_blockU hcs hK.a3
  have hUK : blockU L ≤ K := hK.isA4.le.trans hK.L_le_K
  have hUx : conjR (blockU L) x ≤ blockU L := by
    intro y hy
    have hu : x * y * x⁻¹ ∈ blockU L := mem_conjR.mp hy
    have hgu : (x * y * x⁻¹) * g = g * (x * y * x⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hgC (x * y * x⁻¹) (hUK hu)
    have h1 : g * (x * y * x⁻¹) * g⁻¹ = x * y * x⁻¹ := by
      calc g * (x * y * x⁻¹) * g⁻¹ = ((x * y * x⁻¹) * g) * g⁻¹ := by rw [hgu]
        _ = x * y * x⁻¹ := by group
    have hy' : y = r * (x * y * x⁻¹) * r⁻¹ := by
      rw [hgr] at h1
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = x⁻¹ * (x * r * (x * y * x⁻¹) * (x * r)⁻¹) * x := by rw [h1]
        _ = r * (x * y * x⁻¹) * r⁻¹ := by group
    rw [hy']
    exact (Subgroup.mem_normalizer_iff.mp (hUnorm hrR) _).mp hu
  exact hK.x_good fun y hy => Subgroup.mem_centralizer_iff.mpr fun v hv =>
    hK.isA4.comm_U v hv y (hUx hy)

theorem card_mulAut_alt6 {K : Type*} [Group K] (e₀ : K ≃* alternatingGroup (Fin 6)) :
    Nat.card (MulAut K) = 1440 := by
  obtain ⟨ψ, -⟩ := exists_psl_equiv
  have h1 : Nat.card (MulAut K) = Nat.card (MulAut ↥A6Models.psl29) :=
    Nat.card_congr (MulAut.congr (e₀.trans ψ.symm)).toEquiv
  have hbij : Function.Bijective conjAut := ⟨conjAut_injective, conjAut_surjective⟩
  rw [h1, ← Nat.card_congr (Equiv.ofBijective _ hbij), card_autA6]

theorem isCyclic_of_card_four {P : Type*} [Group P] [Finite P] (hcard : Nat.card P = 4) (z : P)
    (h : ∀ y : P, y * y = 1 → y = 1 ∨ y = z) : IsCyclic P := by
  by_contra hnc
  have hord : ∀ g : P, g * g = 1 := by
    intro g
    have hdvd : orderOf g ∣ 4 := hcard ▸ orderOf_dvd_natCard g
    have hne : orderOf g ≠ 4 := fun h4 =>
      hnc (isCyclic_of_orderOf_eq_card g (by rw [h4, hcard]))
    have h24 : orderOf g ∣ 2 := by
      obtain ⟨i, hi, hgi⟩ :=
        (Nat.dvd_prime_pow Nat.prime_two).mp (by simpa using hdvd : orderOf g ∣ 2 ^ 2)
      interval_cases i
      · rw [hgi]; norm_num
      · rw [hgi]; norm_num
      · exact absurd (by rw [hgi]; norm_num) hne
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp h24
  have hsurj : Function.Surjective (fun b : Bool => if b then (1 : P) else z) := by
    intro g
    rcases h g (hord g) with h1 | h1
    · exact ⟨true, by simp [h1]⟩
    · exact ⟨false, by simp [h1]⟩
  have h2 := Nat.card_le_card_of_surjective _ hsurj
  have h3 : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  omega

theorem lemma2_4_36_of_claim1
    (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (h34 : Lemma2_4_34_used) (hclaim : Lemma2_4_36_claim1) : Lemma2_4_36 := by
  intro G _ _ T M H S L s x z₁ z₂ K hK
  have hclaim' := hclaim G T M H S L s x z₁ z₂ K hK
  have hcs := hK.cs
  obtain ⟨hp1, hR64⟩ := hK.part_one hD h27_1 h34 hclaim'
  have hTC := hK.blockTC_eq_bot hD h27_1 h34 hclaim'
  have hB := basic31 hD h27_1 hK.toA3A3
  obtain ⟨e₀⟩ := hK.nonempty_alt6 h34
  have hT256 : Nat.card T = 2 ^ 8 := by rw [hB.card_T, hR64]; norm_num
  have hS₁card : Nat.card (sOne S x) = 128 := by
    have h1 : Nat.card (sOne S x) = Nat.card (baum S) * (baum S).relIndex (sOne S x) :=
      C5.card_eq_card_mul_relIndex (le_sup_left : baum S ≤ sOne S x)
    rw [h1, hK.relIndex_baum_sOne hD h27_1, hR64]
  obtain ⟨-, hS₁syl, -⟩ := remark31_G₂ hD h27_1 hK.toA3A3x
  have hsurj := lemma2_4_36_surj_of_34 hD h27_1 h34 G T M H S L s x z₁ z₂ K hK
  have hG₂N : centralizerElem z₂ ≤ Subgroup.normalizer (K : Set G) := hK.K_norm
  have hBG : centralizerElem z₂ ⊓ Subgroup.centralizer (K : Set G) ≤ centralizerElem z₂ :=
    inf_le_left
  have hBn : centralizerElem z₂ ≤ Subgroup.normalizer
      ((centralizerElem z₂ ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := by
    intro g hg
    exact C5.mem_normalizer_inf (Subgroup.le_normalizer hg)
      (C5.mem_normalizer_centralizer (hG₂N hg))
  have hSB : IsSylowTwoOf (sOne S x ⊓ (centralizerElem z₂ ⊓ Subgroup.centralizer (K : Set G)))
      (centralizerElem z₂ ⊓ Subgroup.centralizer (K : Set G)) :=
    A4.isSylowTwoOf_inf_normal hS₁syl hBG hBn
  let ρ : ↥(centralizerElem z₂) →* MulAut ↥K :=
    K.normalizerMonoidHom.comp (Subgroup.inclusion hG₂N)
  have hρ : Function.Surjective ρ := by
    intro α
    obtain ⟨g, hg, hα⟩ := hsurj α
    refine ⟨⟨g⁻¹, (centralizerElem z₂).inv_mem hg⟩, ?_⟩
    ext k
    show ((ρ ⟨g⁻¹, _⟩ k : ↥K) : G) = _
    rw [hα k]
    show g⁻¹ * (k : G) * g⁻¹⁻¹ = g⁻¹ * (k : G) * g
    rw [inv_inv]
  have hker : ρ.ker = (centralizerElem z₂ ⊓ Subgroup.centralizer (K : Set G)).subgroupOf
      (centralizerElem z₂) := by
    ext g
    constructor
    · intro hg
      have h1 : ρ g = 1 := hg
      refine ⟨g.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      have h2 := congrArg (fun γ : MulAut ↥K => ((γ ⟨k, hk⟩ : ↥K) : G)) h1
      simp only [MulAut.one_apply] at h2
      have h3 : (g : G) * k * (g : G)⁻¹ = k := h2
      calc k * (g : G) = ((g : G) * k * (g : G)⁻¹) * (g : G) := by rw [h3]
        _ = (g : G) * k := by group
    · intro hg
      have hgC : (g : G) ∈ Subgroup.centralizer (K : Set G) := hg.2
      show ρ g = 1
      ext k
      show (g : G) * (k : G) * (g : G)⁻¹ = k
      have := Subgroup.mem_centralizer_iff.mp hgC k k.2
      calc (g : G) * (k : G) * (g : G)⁻¹ = ((k : G) * g) * (g : G)⁻¹ := by rw [this]
        _ = k := by group
  have h2part := twoPart_eq_of_surjective ρ hρ hker hBG (card_mulAut_alt6 e₀)
  have hcardSB : Nat.card ↥(sOne S x ⊓ (centralizerElem z₂ ⊓ Subgroup.centralizer (K : Set G))) = 4 := by
    have h1 := hSB.card_eq
    have h3 := hS₁syl.card_eq
    rw [hS₁card, h2part, ← h1] at h3
    omega
  have hPeq : sOne S x ⊓ (centralizerElem z₂ ⊓ Subgroup.centralizer (K : Set G)) =
      baum S ⊓ Subgroup.centralizer (K : Set G) := by
    refine le_antisymm ?_ ?_
    · rintro g ⟨hgS₁, -, hgC⟩
      exact ⟨hK.sOne_inf_centralizer_le hD h27_1 ⟨hgS₁, hgC⟩, hgC⟩
    · rintro g ⟨hgR, hgC⟩
      exact ⟨(le_sup_left : baum S ≤ sOne S x) hgR, hK.toA3A3x.baum_le_cent₂ hgR, hgC⟩
  rw [hPeq] at hSB hcardSB
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs hK.a3
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hK.s_mem
  have hU₂B : blockU2 L s ≤ baum S :=
    (C5.conjSubgroup_mono hUB s).trans (le_of_eq (C5.conjSubgroup_eq_self hsB))
  have hz₂R : z₂ ∈ baum S := hU₂B hK.toA3A3x.z₂_mem.1
  have hz₂C : z₂ ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mp (hK.K_comp.1 hk)
  have hcyc : IsCyclic ↥(baum S ⊓ Subgroup.centralizer (K : Set G)) :=
    isCyclic_of_card_four hcardSB ⟨z₂, hz₂R, hz₂C⟩ (fun y hy => by
      have := hclaim' (y : G) y.2 (by
        have := congrArg Subtype.val hy
        simpa using this)
      rcases this with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h)
  have hle := le_of_cyclic_sylow_of_oddCoreIn_eq_bot hBG hBn hSB hcyc
    (oddCoreIn_centralizer₂_eq_bot hD h27_1 hK.toA3A3x)
  refine ⟨hp1, ⟨?_, hcyc, hcardSB, hsurj⟩, hTC, hT256⟩
  refine le_antisymm (fun g hg => ?_) (fun g hg => ⟨hK.toA3A3x.baum_le_cent₂ hg.1, hg.2⟩)
  exact hle ⟨hg.1, hg.2⟩

end Config

end CFSG.QuasithinUnique.DoubleA3
