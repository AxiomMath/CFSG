module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3RemarkC
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Core
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PlaneInT
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3RemarkAux

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

private theorem frattini_split {p : ℕ} [Fact p.Prime] {Y S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf p S Y) {g : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    ∃ k ∈ Y, ∃ m ∈ Subgroup.normalizer (S : Set G), g = k * m := by
  have hS' : CFSG.ABGLocalTools.IsSylowOf p (S.map (MulAut.conj g).toMonoidHom) Y := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hg s).1 (hS.le hs)
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hS.card_eq]
  obtain ⟨k, hk, hconj⟩ := hS.exists_mem_conj hS'
  have hkx : k⁻¹ * g ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have e1 : g * s * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom ↔ s ∈ S := by
      constructor
      · rintro ⟨t, ht, hts⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hts
        exact mul_left_cancel (mul_right_cancel hts) ▸ ht
      · exact fun hs => ⟨s, hs, rfl⟩
    have e2 := hconj (g * s * g⁻¹)
    rw [e1, show k⁻¹ * (g * s * g⁻¹) * k = (k⁻¹ * g) * s * (k⁻¹ * g)⁻¹ by group] at e2
    exact e2
  exact ⟨k, hk, k⁻¹ * g, hkx, by group⟩

private theorem exists_mul_of_mem_sup {A B : Subgroup G}
    (hB : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) {g : G} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * (b₁ * a₂ * b₁⁻¹), A.mul_mem ha₁ (hB b₁ hb₁ a₂ ha₂), b₁ * b₂,
          B.mul_mem hb₁ hb₂, ?_⟩
        group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨b⁻¹ * a⁻¹ * b, ?_, b⁻¹, B.inv_mem hb, by group⟩
        have := hB b⁻¹ (B.inv_mem hb) a⁻¹ (A.inv_mem ha)
        simpa using this }
  have hAS : A ≤ S := fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩
  have hBS : B ≤ S := fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩
  exact sup_le hAS hBS hg

private theorem u3T_le_C : u3T P x J ≤ Subgroup.centralizer ({x} : Set G) :=
  (inf_le_left : u3T P x J ≤ u3S P x).trans inf_le_right

private theorem u3K0_le_C : u3K0 p x J ≤ Subgroup.centralizer ({x} : Set G) :=
  fun _ hk => hk.1

private theorem mem_normalizer_T {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J) {m : G}
    (hmP : m ∈ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hmC : m ∈ Subgroup.centralizer ({x} : Set G)) :
    m ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) := by
  have h1 : m ∈ Subgroup.normalizer (((P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) :
      Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hmP, Subgroup.le_normalizer hmC⟩
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, hc.cent_le hmC⟩

private theorem K0_centralizes_T {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J) {k : G} (hk : k ∈ u3K0 p x J)
    (hkN : k ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G)) :
    ∀ t ∈ u3T P x J, k * t * k⁻¹ = t := by
  intro t ht
  have h1 : k * t * k⁻¹ * t⁻¹ ∈ u3T P x J :=
    (u3T P x J).mul_mem ((Subgroup.mem_normalizer_iff.mp hkN t).mp ht) ((u3T P x J).inv_mem ht)
  have h2 : k * t * k⁻¹ * t⁻¹ ∈ u3K0 p x J := by
    have := (u3K0 p x J).mul_mem hk
      (u3K0_conj_gen3 hc t (u3T_le_C ht) k⁻¹ ((u3K0 p x J).inv_mem hk))
    simpa [mul_assoc] using this
  have h3 : k * t * k⁻¹ * t⁻¹ ∈ u3T P x J ⊓ u3K0 p x J := ⟨h1, h2⟩
  rw [u3_T_inf_K0_gen3 hc, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.mp h3

theorem u3_frattini_NC_gen3 {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    (hPdec : (P : Subgroup G) ≤ u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J)) :
    ∀ n ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ⊓ J,
      ∃ e ∈ u3T P x J ⊔ u3K0 p x J, ∃ m ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ({x} : Set G), n = e * m := by
  intro n hn
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨hnT, hnJ⟩ := Subgroup.mem_inf.mp hn
  have hnC : n ∈ Subgroup.centralizer ({x} : Set G) := hc.le_cent hnJ
  have hnK : n ∈ Subgroup.normalizer ((u3K0 p x J : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact u3K0_conj_gen3 hc n hnC k hk
    · intro hk
      have := u3K0_conj_gen3 hc n⁻¹ (Subgroup.inv_mem _ hnC) _ hk
      simpa [mul_assoc] using this
  have hnE : n ∈ Subgroup.normalizer ((u3T P x J ⊔ u3K0 p x J : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hnT, hnK⟩
  have hPE : (P : Subgroup G) ≤ u3T P x J ⊔ u3K0 p x J :=
    hPdec.trans (sup_le_sup_left inf_le_right _)
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup G) (u3T P x J ⊔ u3K0 p x J) :=
    ⟨P.subtype hPE, by rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPE]⟩
  obtain ⟨e, he, m, hm, rfl⟩ := frattini_split hsyl hnE
  have heC : e ∈ Subgroup.centralizer ({x} : Set G) := by
    have hle : u3T P x J ⊔ u3K0 p x J ≤ Subgroup.centralizer ({x} : Set G) :=
      sup_le u3T_le_C u3K0_le_C
    exact hle he
  have hmC : m ∈ Subgroup.centralizer ({x} : Set G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ heC) hnC
    simpa using this
  exact ⟨e, he, m, Subgroup.mem_inf.mpr ⟨hm, hmC⟩, rfl⟩

private theorem exists_pcomplement {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) (N : Subgroup G)
    (hPN : (P : Subgroup G) ≤ N) (hNP : N ≤ Subgroup.normalizer ((P : Subgroup G) : Set G)) :
    ∃ F : Subgroup G, F ≤ N ∧ (∀ m ∈ N, ∃ s ∈ (P : Subgroup G), ∃ f ∈ F, m = s * f) ∧
      ∃ s : ℕ, Nat.Coprime p s ∧ ∀ f ∈ F, f ^ s = 1 := by
  haveI hnorm : ((P : Subgroup G).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).mpr hNP
  have hndvd : ¬ p ∣ ((P : Subgroup G).subgroupOf N).index := by
    intro h
    exact P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hPN))
  have hcard : Nat.card ((P : Subgroup G).subgroupOf N) =
      p ^ (Nat.card G).factorization p := by
    rw [← P.card_eq_multiplicity]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
  have hcop : Nat.Coprime (Nat.card ((P : Subgroup G).subgroupOf N))
      ((P : Subgroup G).subgroupOf N).index := by
    rw [hcard]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hndvd)
  obtain ⟨F₀, hF₀⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  refine ⟨F₀.map N.subtype, Subgroup.map_subtype_le F₀, ?_, ?_⟩
  · intro m hm
    obtain ⟨⟨s', f'⟩, hsf⟩ := hF₀.2 ⟨m, hm⟩
    refine ⟨((s' : N) : G), s'.2, ((f' : N) : G), ⟨f', f'.2, rfl⟩, ?_⟩
    have := congrArg Subtype.val hsf
    simpa using this.symm
  · refine ⟨Nat.card F₀, ?_, ?_⟩
    · have := hF₀.symm.index_eq_card
      rw [← this]
      exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hndvd
    · rintro _ ⟨f', hf', rfl⟩
      have h1 : (⟨f', hf'⟩ : F₀) ^ Nat.card F₀ = 1 := pow_card_eq_one'
      have h2 : f' ^ Nat.card F₀ = 1 := congrArg Subtype.val h1
      show ((f' : N) : G) ^ Nat.card F₀ = 1
      rw [← Subgroup.coe_pow, h2]
      rfl

private theorem comm_mem_zOf {p : ℕ} [hp : Fact p.Prime] {T : Subgroup G}
    (hcard : Nat.card T = p ^ 3) (hnc : ¬ IsMulCommutative T) :
    ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ zOf T := by
  have hZ : Nat.card (Subgroup.center T) = p := card_center_of_nonabelian_card_p_cube hcard hnc
  have hq : Nat.card (T ⧸ Subgroup.center T) = p ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center T)
    rw [hcard, hZ] at h
    apply Nat.eq_of_mul_eq_mul_right hp.out.pos
    rw [← h]
    ring
  have hcomm : IsMulCommutative (T ⧸ Subgroup.center T) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  intro a ha b hb
  have key : ((⟨a, ha⟩ : T) * ⟨b, hb⟩ * (⟨a, ha⟩ : T)⁻¹ * (⟨b, hb⟩ : T)⁻¹ : T) ∈
      Subgroup.center T := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [IsMulCommutative.is_comm.comm ((⟨a, ha⟩ : T) : T ⧸ Subgroup.center T)
      ((⟨b, hb⟩ : T) : T ⧸ Subgroup.center T)]
    group
  refine ⟨T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha)) (T.inv_mem hb),
    Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp key ⟨t, ht⟩)

private theorem NJ_action {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    (hpd : PGroupData p (P : Subgroup G) (u3T P x J) ((P : Subgroup G) ⊓ u3K0 p x J) x)
    (hPdec : (P : Subgroup G) ≤ u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J)) {F : Subgroup G}
    (hFdec : ∀ m ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
      Subgroup.centralizer ({x} : Set G), ∃ s ∈ (P : Subgroup G), ∃ f ∈ F, m = s * f)
    (hFT : ∀ f ∈ F, ∀ t ∈ u3T P x J, f * t * f⁻¹ ∈ u3T P x J) :
    ∀ n ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ⊓ J,
      ∃ τ ∈ u3T P x J, ∃ f ∈ F, ∀ t ∈ u3T P x J, n * t * n⁻¹ = τ * (f * t * f⁻¹) * τ⁻¹ := by
  intro n hn
  have pd := hpd
  have hnN : n ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hn).1
  obtain ⟨e, he, m, hm, hnem⟩ := u3_frattini_NC_gen3 hc hP hPdec n hn
  obtain ⟨hmP, hmC⟩ := Subgroup.mem_inf.mp hm
  have hmN : m ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) :=
    mem_normalizer_T hc hmP hmC
  have heN : e ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) := by
    have h1 : e = n * m⁻¹ := by rw [hnem]; group
    rw [h1]
    exact Subgroup.mul_mem _ hnN (Subgroup.inv_mem _ hmN)
  obtain ⟨s, hsP, f, hfF, hmsf⟩ := hFdec m hm
  have he' : e ∈ u3K0 p x J ⊔ u3T P x J := by rwa [sup_comm] at he
  obtain ⟨k, hk, t₁, ht₁, hekt⟩ := exists_mul_of_mem_sup
    (fun b hb a ha => u3K0_conj_gen3 hc b (u3T_le_C hb) a ha) he'
  have hkN : k ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) := by
    have h1 : k = e * t₁⁻¹ := by rw [hekt]; group
    rw [h1]
    exact Subgroup.mul_mem _ heN (Subgroup.inv_mem _ (Subgroup.le_normalizer ht₁))
  have hkc := K0_centralizes_T hc hk hkN
  have hsTD : s ∈ u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J) := by rw [pd.sup_eq]; exact hsP
  obtain ⟨t₀, ht₀, d₀, hd₀, hstd⟩ := exists_mul_of_mem_sup
    (fun b hb a ha => by rw [← pd.comm a ha b hb]; simpa using ha) hsTD
  refine ⟨t₁ * t₀, (u3T P x J).mul_mem ht₁ ht₀, f, hfF, fun t ht => ?_⟩
  have hy : f * t * f⁻¹ ∈ u3T P x J := hFT f hfF t ht
  have hd : d₀ * (f * t * f⁻¹) * d₀⁻¹ = f * t * f⁻¹ := by
    rw [← pd.comm _ hy d₀ hd₀]
    group
  have hz : (t₁ * t₀) * (f * t * f⁻¹) * (t₁ * t₀)⁻¹ ∈ u3T P x J :=
    (u3T P x J).mul_mem ((u3T P x J).mul_mem ((u3T P x J).mul_mem ht₁ ht₀) hy)
      ((u3T P x J).inv_mem ((u3T P x J).mul_mem ht₁ ht₀))
  rw [hnem, hmsf, hekt, hstd]
  calc k * t₁ * (t₀ * d₀ * f) * t * (k * t₁ * (t₀ * d₀ * f))⁻¹
      = k * ((t₁ * t₀) * (d₀ * (f * t * f⁻¹) * d₀⁻¹) * (t₁ * t₀)⁻¹) * k⁻¹ := by group
    _ = k * ((t₁ * t₀) * (f * t * f⁻¹) * (t₁ * t₀)⁻¹) * k⁻¹ := by rw [hd]
    _ = (t₁ * t₀) * (f * t * f⁻¹) * (t₁ * t₀)⁻¹ := hkc _ hz

private theorem zOf_conj_mem {T : Subgroup G} {f : G} (hf : f ∈ Subgroup.normalizer (T : Set G))
    {z : G} (hz : z ∈ zOf T) : f * z * f⁻¹ ∈ zOf T := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hf z).mp hz.1,
    Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
  have ht' : f⁻¹ * t * f ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hf) t).mp ht
    simpa using this
  have hc' := Subgroup.mem_centralizer_iff.mp hz.2 _ ht'
  calc t * (f * z * f⁻¹) = f * ((f⁻¹ * t * f) * z) * f⁻¹ := by group
    _ = f * (z * (f⁻¹ * t * f)) * f⁻¹ := by rw [hc']
    _ = f * z * f⁻¹ * t := by group

theorem u3_exists_Fhat_gen3 {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hS : Setting G)
    (hc : PointConfig3 Typ G p P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    (hpd : PGroupData p (P : Subgroup G) (u3T P x J) ((P : Subgroup G) ⊓ u3K0 p x J) x)
    (hPdec : (P : Subgroup G) ≤ u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J))
    (hNJ : TorusProps p (u3T P x J) (Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ⊓ J)) :
    ∃ F : Subgroup G, F ≤ M ∧ TorusProps p (u3T P x J) F ∧
      ∀ f ∈ F, ∀ d ∈ (P : Subgroup G) ⊓ u3K0 p x J, f * d * f⁻¹ = d := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  have pd := hpd
  obtain ⟨F, hFN, hFdec, s, hs, hFs⟩ := exists_pcomplement P
    (Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓ Subgroup.centralizer ({x} : Set G))
    (le_inf Subgroup.le_normalizer hP) inf_le_left
  have hNM := CFSG.LocalAnalysis.RankThreeTheoremC.normalizer_sylow_le hS hc.sigma hc.core
  have hFT : ∀ f ∈ F, ∀ t ∈ u3T P x J, f * t * f⁻¹ ∈ u3T P x J := fun f hf t ht => by
    obtain ⟨hfP, hfC⟩ := Subgroup.mem_inf.mp (hFN hf)
    exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_T hc hfP hfC) t).mp ht
  have hTcomm := comm_mem_zOf pd.T_card pd.T_nonab
  have hact := NJ_action hc hP hpd hPdec hFdec hFT
  refine ⟨F, fun f hf => hNM (Subgroup.mem_inf.mp (hFN hf)).1, ⟨hFT, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro A hAT hZA hAF
    refine hNJ.irred A hAT hZA ?_
    intro n hn a ha
    obtain ⟨τ, hτ, f, hf, hnt⟩ := hact n hn
    rw [hnt a (hAT ha)]
    have h1 : f * a * f⁻¹ ∈ A := hAF f hf a ha
    have h2 := hTcomm τ hτ _ (hAT h1)
    have h3 : τ * (f * a * f⁻¹) * τ⁻¹ =
        (τ * (f * a * f⁻¹) * τ⁻¹ * (f * a * f⁻¹)⁻¹) * (f * a * f⁻¹) := by group
    rw [h3]
    exact A.mul_mem (hZA h2) h1
  ·
    intro t ht hFt
    refine hNJ.fpf t ht ?_
    intro n hn
    obtain ⟨τ, hτ, f, hf, hnt⟩ := hact n hn
    rw [hnt t ht]
    have h2 := hTcomm τ hτ _ (hFT f hf t ht)
    have h3 := hFt f hf
    have h4 : τ * (f * t * f⁻¹) * τ⁻¹ * t⁻¹ =
        (τ * (f * t * f⁻¹) * τ⁻¹ * (f * t * f⁻¹)⁻¹) * (f * t * f⁻¹ * t⁻¹) := by group
    rw [h4]
    exact (zOf (u3T P x J)).mul_mem h2 h3
  ·
    intro z hz k hk
    obtain ⟨n, hn, hnz⟩ := hNJ.onto z hz k hk
    obtain ⟨τ, hτ, f, hf, hnt⟩ := hact n hn
    refine ⟨f, hf, ?_⟩
    have hfN : f ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) := by
      obtain ⟨hfP, hfC⟩ := Subgroup.mem_inf.mp (hFN hf)
      exact mem_normalizer_T hc hfP hfC
    have hfz := zOf_conj_mem hfN hz
    rw [← hnz, hnt z hz.1]
    have h5 := Subgroup.mem_centralizer_iff.mp hfz.2 τ hτ
    rw [h5]
    group
  ·
    intro f hf d hd
    haveI : IsCyclic ↥((P : Subgroup G) ⊓ u3K0 p x J) := pd.D_cyc
    obtain ⟨hfP, hfC⟩ := Subgroup.mem_inf.mp (hFN hf)
    refine cyclic_coprime_aut_trivial hc.prime ?_ pd.x_mem pd.x_ord ?_ ?_ hs ?_ d hd
    · intro d' hd'
      obtain ⟨j, hj⟩ := P.isPGroup' ⟨d', hd'.1⟩
      exact ⟨j, congrArg Subtype.val hj⟩
    · intro d' hd'
      exact ⟨(Subgroup.mem_normalizer_iff.mp hfP d').mp hd'.1, u3K0_conj_gen3 hc f hfC d' hd'.2⟩
    · have h6 := Subgroup.mem_centralizer_iff.mp hfC x (Set.mem_singleton x)
      rw [← h6]
      group
    · intro d' hd'
      rw [hFs f hf]
      simp

private theorem isPGroup_zpowers_of_pow_eq_one' {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] {g : Y}
    {k : ℕ} (hg : g ^ (p ^ k) = 1) : IsPGroup p (Subgroup.zpowers g) := by
  obtain ⟨m, -, hm'⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hg)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm'])

private theorem two_le_pRank_of_typeTStruct {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J) (hTstr : TypeTStruct p P x J) :
    2 ≤ CFSG.Open.pRank p (u3T P x J) := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨hTcard, hTexp, hTnab, -⟩ := id hTstr
  obtain ⟨E, hET, hE, hEcard, -⟩ := exists_isElemAbelian_card_sq_of_nonabelian hTcard hTexp hTnab
  exact le_pRank_of_elemAbelian_card hET hE hEcard

theorem u3_pElement_MJ_core3 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig3 Typ G p P M x J)
    (h2 : 2 ≤ CFSG.Open.pRank p (u3T P x J)) (hmax : TypeBorelMax Typ p) :
    ∀ g ∈ M ⊓ J, (∃ k : ℕ, g ^ (p ^ k) = 1) → g ∈ u3T P x J ⊔ rankThreePrimeCore p J := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hTP : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  have hTM : u3T P x J ≤ M := hTP.trans hPM
  have hTp : IsPGroup p (u3T P x J) := P.isPGroup'.to_le hTP
  have hNT : Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hc.sigma hc.core hTp hTM h2
  have hOM : rankThreePrimeCore p J ≤ M :=
    (u3main_core_facts hS hD1 hc.sigma hc.core hc.generic hc.le_cent hc.cent_le).1
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ, honto⟩ := u3_normalizer_onto_gen3 hc
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hSylJ : CFSG.ABGLocalTools.IsSylowOf p (u3T P x J) J :=
    hc.generic.2.2.1.inf_of_le_normalizer hc.le_cent hc.cent_le
  obtain ⟨Tsyl, hTsyl⟩ := hSylJ.exists_sylow_eq_subgroupOf
  let Tsyl' : Sylow p Q := Tsyl.mapSurjective hψ
  have hTsyl' : (Tsyl' : Subgroup Q) = ((u3T P x J).subgroupOf J).map ψ := by
    rw [← hTsyl]; exact Sylow.coe_mapSurjective hψ Tsyl
  have hmaxS := hmax Q hQ Tsyl'
  set A : Subgroup Q := (M.subgroupOf J).map ψ
  have hNA : Subgroup.normalizer ((Tsyl' : Subgroup Q) : Set Q) ≤ A := by
    intro q hq
    rw [hTsyl'] at hq
    obtain ⟨n, hnN, hnJ, hψn⟩ := honto q hq
    exact ⟨⟨n, hnJ⟩, hNT hnN.1, hψn⟩
  rcases (hmaxS A hNA).symm with hAtop | hAeq
  · exfalso
    apply hc.not_le
    intro j hj
    have hmem : ψ ⟨j, hj⟩ ∈ A := hAtop ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hψm⟩ := hmem
    have hk : m⁻¹ * ⟨j, hj⟩ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψm, inv_mul_cancel]
    rw [hker] at hk
    have hk' : ((m⁻¹ * ⟨j, hj⟩ : J) : G) ∈ rankThreePrimeCore p J := hk
    have hjm : j = (m : G) * (((m⁻¹ * ⟨j, hj⟩ : J)) : G) := by simp
    rw [hjm]
    exact M.mul_mem hm (hOM hk')
  · intro g hg hgp
    obtain ⟨hgM, hgJ⟩ := hg
    obtain ⟨k, hk⟩ := hgp
    have hψg : ψ ⟨g, hgJ⟩ ∈ Subgroup.normalizer ((Tsyl' : Subgroup Q) : Set Q) := by
      rw [← hAeq]; exact ⟨⟨g, hgJ⟩, hgM, rfl⟩
    have hpe : (ψ ⟨g, hgJ⟩) ^ (p ^ k) = 1 := by
      rw [← map_pow]
      have : (⟨g, hgJ⟩ : J) ^ (p ^ k) = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]
    have hzp : IsPGroup p (Subgroup.zpowers (ψ ⟨g, hgJ⟩)) :=
      isPGroup_zpowers_of_pow_eq_one' hp hpe
    have hmem : ψ ⟨g, hgJ⟩ ∈ (Tsyl' : Subgroup Q) := by
      have h1 : ψ ⟨g, hgJ⟩ ∈ Subgroup.zpowers (ψ ⟨g, hgJ⟩) ⊓
          Subgroup.normalizer ((Tsyl' : Subgroup Q) : Set Q) := ⟨Subgroup.mem_zpowers _, hψg⟩
      have h2 := hzp.inf_normalizer_sylow Tsyl'
      have h3 : ψ ⟨g, hgJ⟩ ∈ Subgroup.zpowers (ψ ⟨g, hgJ⟩) ⊓ (Tsyl' : Subgroup Q) := by
        rw [← h2]; exact h1
      exact h3.2
    rw [hTsyl'] at hmem
    obtain ⟨t, ht, hψt⟩ := hmem
    have hk2 : t⁻¹ * ⟨g, hgJ⟩ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψt, inv_mul_cancel]
    rw [hker] at hk2
    have hk2' : ((t⁻¹ * ⟨g, hgJ⟩ : J) : G) ∈ rankThreePrimeCore p J := hk2
    have hgt : g = (t : G) * (((t⁻¹ * ⟨g, hgJ⟩ : J)) : G) := by simp
    rw [hgt]
    exact Subgroup.mul_mem_sup ht hk2'

theorem u3_W_le_normalizer_core3 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig3 Typ G p P M x J)
    (h2 : 2 ≤ CFSG.Open.pRank p (u3T P x J)) (hTexp : ∀ t ∈ u3T P x J, t ^ p = 1)
    (hmax : TypeBorelMax Typ p) :
    M ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((u3T P x J ⊔ u3K0 p x J : Subgroup G) : Set G) := by
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hTP : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  have hTJ : u3T P x J ≤ J := inf_le_right
  have key : ∀ w ∈ M ⊓ Subgroup.centralizer ({x} : Set G), ∀ s ∈ u3T P x J ⊔ u3K0 p x J,
      w * s * w⁻¹ ∈ u3T P x J ⊔ u3K0 p x J := by
    intro w hw s hs
    have hle : u3T P x J ⊔ u3K0 p x J ≤
        (u3T P x J ⊔ u3K0 p x J).comap (MulAut.conj w).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro t ht
        have hwtM : w * t * w⁻¹ ∈ M :=
          M.mul_mem (M.mul_mem hw.1 (hPM (hTP ht))) (M.inv_mem hw.1)
        have hwtJ : w * t * w⁻¹ ∈ J :=
          ((Subgroup.mem_normalizer_iff.mp (hc.cent_le hw.2) t).mp (hTJ ht))
        have hpe : (w * t * w⁻¹) ^ (p ^ 1) = 1 := by
          rw [pow_one, conj_pow, hTexp t ht]; simp
        have h1 := u3_pElement_MJ_core3 hS hD1 hU0 hc h2 hmax _ ⟨hwtM, hwtJ⟩ ⟨1, hpe⟩
        exact sup_le_sup_left (u3_core_le_K0_gen3 hc) _ h1
      · intro k hk
        exact Subgroup.mem_sup_right (u3K0_conj_gen3 hc w hw.2 k hk)
    exact hle hs
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨key w hw s, fun h => ?_⟩
  have h1 := key w⁻¹ (inv_mem hw) _ h
  simpa [mul_assoc] using h1

theorem u3_centSeries_core3 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig3 Typ G p P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    (h2 : 2 ≤ CFSG.Open.pRank p (u3T P x J)) (hTexp : ∀ t ∈ u3T P x J, t ^ p = 1)
    (hmax : TypeBorelMax Typ p) (hDcyc : IsCyclic ↥((P : Subgroup G) ⊓ u3K0 p x J))
    (hxD : x ∈ (P : Subgroup G) ⊓ u3K0 p x J) (hxo : orderOf x = p)
    (hdec : (P : Subgroup G) ≤ u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J)) :
    ∃ N : Subgroup G, CentSeries p (M ⊓ Subgroup.centralizer ({x} : Set G)) (P : Subgroup G) N := by
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hPW : (P : Subgroup G) ≤ M ⊓ Subgroup.centralizer ({x} : Set G) := le_inf hPM hP
  have hTP : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  obtain ⟨N₀, -, hN₀C, hN₀cop, hK⟩ := u3_K0_pComplement_core3 hc hP hDcyc hxD hxo
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer (N₀ : Set G) := by
    intro c hc'
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hN₀C c (hP hc') n hn, fun hn => ?_⟩
    have h1 := hN₀C c⁻¹ (Subgroup.inv_mem _ (hP hc')) _ hn
    simpa [mul_assoc] using h1
  have hprod : ((P : Subgroup G) ⊔ N₀ : Subgroup G) = ((P : Subgroup G) : Set G) * (N₀ : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hPN
  have hTK : u3T P x J ⊔ u3K0 p x J ≤ (P : Subgroup G) ⊔ N₀ := by
    refine sup_le (hTP.trans le_sup_left) ?_
    intro k hk
    obtain ⟨n, hn, d, hd, rfl⟩ := hK k hk
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hn) (Subgroup.mem_sup_left hd.1)
  have hPTK : (P : Subgroup G) ≤ u3T P x J ⊔ u3K0 p x J :=
    hdec.trans (sup_le_sup_left inf_le_right _)
  refine ⟨(M ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ N₀, hPW, inf_le_left, ?_, ?_, ?_⟩
  · intro c hcW n hn
    exact ⟨(M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem
      ((M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem hcW hn.1)
      ((M ⊓ Subgroup.centralizer ({x} : Set G)).inv_mem hcW), hN₀C c hcW.2 n hn.2⟩
  · intro c hcW q hq
    have hle : (P : Subgroup G) ⊔ (M ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ N₀ ≤
        ((P : Subgroup G) ⊔ (M ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ N₀).comap
          (MulAut.conj c).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro a ha
        have hcaW : c * a * c⁻¹ ∈ M ⊓ Subgroup.centralizer ({x} : Set G) :=
          (M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem
            ((M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem hcW (hPW ha))
            ((M ⊓ Subgroup.centralizer ({x} : Set G)).inv_mem hcW)
        have hnorm := u3_W_le_normalizer_core3 hS hD1 hU0 hc h2 hTexp hmax hcW
        have hcaTK : c * a * c⁻¹ ∈ u3T P x J ⊔ u3K0 p x J :=
          (Subgroup.mem_normalizer_iff.mp hnorm a).mp (hPTK ha)
        have hcaPN : c * a * c⁻¹ ∈ ((P : Subgroup G) ⊔ N₀ : Subgroup G) := hTK hcaTK
        have hcaPN' : c * a * c⁻¹ ∈ ((P : Subgroup G) : Set G) * (N₀ : Set G) := by
          rw [← hprod]; exact hcaPN
        obtain ⟨a', ha', n', hn', hEq⟩ := hcaPN'
        have hn'W : n' ∈ M ⊓ Subgroup.centralizer ({x} : Set G) := by
          have : n' = a'⁻¹ * (c * a * c⁻¹) := by rw [← hEq]; simp
          rw [this]
          exact (M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem
            ((M ⊓ Subgroup.centralizer ({x} : Set G)).inv_mem (hPW ha')) hcaW
        show c * a * c⁻¹ ∈ (P : Subgroup G) ⊔ (M ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ N₀
        rw [← hEq]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha') (Subgroup.mem_sup_right ⟨hn'W, hn'⟩)
      · intro n hn
        have hcn : c * n * c⁻¹ ∈ (M ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ N₀ :=
          ⟨(M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem
            ((M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem hcW hn.1)
            ((M ⊓ Subgroup.centralizer ({x} : Set G)).inv_mem hcW), hN₀C c hcW.2 n hn.2⟩
        exact Subgroup.mem_sup_right hcn
    exact hle hq
  · intro n hn
    exact hN₀cop n hn.2

theorem u3_centSeries_gen3 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig3 Typ G p P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) (hTstr : TypeTStruct p P x J)
    (hmax : TypeBorelMax Typ p)
    (hpd : PGroupData p (P : Subgroup G) (u3T P x J) ((P : Subgroup G) ⊓ u3K0 p x J) x) :
    ∃ N : Subgroup G, CentSeries p (M ⊓ Subgroup.centralizer ({x} : Set G)) (P : Subgroup G) N :=
  u3_centSeries_core3 hS hD1 hU0 hc hP (two_le_pRank_of_typeTStruct hc hTstr) hTstr.2.1
    hmax hpd.D_cyc
    hpd.x_mem hpd.x_ord hpd.sup_eq.ge

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3RemarkAux
