module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CC1Lie
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CFam2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171ExtremalRank
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265C.C1

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open scoped commutatorElement

@[expose] def QSFamCTE6C2 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω), QSNL 3 S B T x D K →
    catalogIs (PSimple 3 K) S9.isTE6two → catalogIs (PSimple 3 S) (fun i => isE7TwoIdx i ∨ isE8TwoIdx i) →
    (∃ T₀ : Subgroup Ω, T₀ ≤ S ∧ IsPGroup 2 T₀ ∧ B ≤ Subgroup.normalizer (T₀ : Set Ω) ∧
      (⁅T₀, B⁆ : Subgroup Ω) ≠ ⊥) →
    QSConcl 3 S B D K

@[expose] def QSFamCTD4C2 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω), QSNL 3 S B T x D K →
    catalogIs (PSimple 3 K) S9.isTD4two → catalogIs (PSimple 3 S) S9.isTE6two →
    (∃ T₀ : Subgroup Ω, T₀ ≤ S ∧ IsPGroup 2 T₀ ∧ B ≤ Subgroup.normalizer (T₀ : Set Ω) ∧
      (⁅T₀, B⁆ : Subgroup Ω) ≠ ⊥) →
    QSConcl 3 S B D K

section Split

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem case1_or_case2 {S B T : Subgroup Ω} (hSn : S.Normal) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hT : IsPGroup 2 T) (hBT : B ≤ Subgroup.normalizer (T : Set Ω))
    (hrank : 3 ^ GLATwoLocalRank 3 Ω ≤ Nat.card B)
    (hmaxc : (⁅T, B⁆ : Subgroup Ω) ≠ ⊥ ∨ ∀ E : Subgroup Ω, IsElemAbelian 3 E → Nat.card E ≤ Nat.card B) :
    (∀ E : Subgroup Ω, IsElemAbelian 3 E → E ≤ S ⊔ B → Nat.card E ≤ Nat.card B) ∨
      ∃ t ∈ T, ∃ c ∈ B, ⁅t, c⁆ ∉ centModSubgroup 3 S := by
  rcases hmaxc with hne | hall
  · by_cases hcomm : ∀ t ∈ T, ∀ c ∈ B, ⁅t, c⁆ ∈ centModSubgroup 3 S
    · left
      intro E hE hES
      have hTB : (⁅T, B⁆ : Subgroup Ω) ≤ T := S12.comm_le_left hBT
      have hTB2 : IsPGroup 2 (⁅T, B⁆ : Subgroup Ω) := hT.to_le hTB
      have hTBc : (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω) := by
        rw [Subgroup.commutator_le]
        intro t ht c hc
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        exact (S267.ModelGen.comm_of_mem_centMod hSn hcore (hcomm t ht c hc) hs).symm
      have hSBN : S ⊔ B ≤ Subgroup.normalizer ((⁅T, B⁆ : Subgroup Ω) : Set Ω) :=
        sup_le ((Subgroup.le_centralizer_iff.1 hTBc).trans (Subgroup.centralizer_le_normalizer _))
          (fun c hc => S12.normalizer_commutator (hBT hc) (Subgroup.le_normalizer hc))
      exact (card_le_pow_glaTwoLocalRank Nat.prime_three hE hne hTB2 (hES.trans hSBN)).trans hrank
    · right
      push Not at hcomm
      exact hcomm
  · exact Or.inl fun E hE _ => hall E hE

private theorem mem_normalizer_sup_of_mem {A C : Subgroup Ω} {c : Ω}
    (hA : c ∈ Subgroup.normalizer (A : Set Ω)) (hC : c ∈ Subgroup.normalizer (C : Set Ω)) :
    c ∈ Subgroup.normalizer ((A ⊔ C : Subgroup Ω) : Set Ω) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hA hC ⊢
  unfold GLBConj at hA hC ⊢
  rw [Subgroup.map_sup, hA, hC]

end Split

section Certs

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exists_two_subgroup_of_case2 {S B T : Subgroup Ω} (hKG : CFSG.Open.IsKGroup Ω)
    (hcomp : GLAPComponent 3 (⊤ : Subgroup Ω) S) (hSn : S.Normal) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hchev : IsChevSimple 2 (PSimple 3 S)) (hB : IsElemAbelian 3 B) (hT : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set Ω))
    (hnc : ∃ t ∈ T, ∃ c ∈ B, ⁅t, c⁆ ∉ centModSubgroup 3 S) :
    ∃ T₀ : Subgroup Ω, T₀ ≤ S ∧ IsPGroup 2 T₀ ∧ B ≤ Subgroup.normalizer (T₀ : Set Ω) ∧
      (⁅T₀, B⁆ : Subgroup Ω) ≠ ⊥ := by
  have hBp : IsPGroup 3 B := isPGroup_of_isElemAbelian hB
  have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 hSn) ▸ Subgroup.mem_top g
  set Z : Subgroup Ω := Subgroup.centralizer (S : Set Ω) with hZdef
  haveI hZn : Z.Normal := Subgroup.normal_centralizer
  have hcZ : ∀ g ∈ centModSubgroup 3 S, g ∈ Z := fun g hg =>
    Subgroup.mem_centralizer_iff.2 fun s hs => (S267.ModelGen.comm_of_mem_centMod hSn hcore hg hs).symm
  set T₁ : Subgroup Ω := ⁅T, B⁆ with hT₁def
  have hT₁T : T₁ ≤ T := S12.comm_le_left hBT
  have hT₁2 : IsPGroup 2 T₁ := hT.to_le hT₁T
  have hBT₁ : B ≤ Subgroup.normalizer (T₁ : Set Ω) := fun c hc =>
    S12.normalizer_commutator (hBT hc) (Subgroup.le_normalizer hc)
  have h712 := i712At_holds Ω 3 Nat.prime_three (by norm_num) ⊤ S B T (HDesc.isKGroup_of_le hKG ⊤) hcomp
    hchev hBp hT (fun g _ => hSN g) (fun g _ => hSN g) hBT
  have hT₁SZ : T₁ ≤ S ⊔ Z := by
    rw [hT₁def, Subgroup.commutator_le]
    intro t ht c hc
    obtain ⟨l, hl, hlc⟩ := S12.exists_centMod_of_inducesInnerMod (h712 c hc t ht)
    have hct : ⁅c, t⁆ ∈ S ⊔ Z := by
      have e : ⁅c, t⁆ = l * (l⁻¹ * ⁅c, t⁆) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right (hcZ _ hlc))
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ hct
  set H : Subgroup Ω := S ⊓ (T₁ ⊔ Z) with hHdef
  set Z' : Subgroup Ω := S ⊓ Z with hZ'def
  haveI : S.Normal := hSn
  haveI hZ'n : Z'.Normal := Subgroup.normal_inf_normal S Z
  have hZ'H : Z' ≤ H := inf_le_inf_left S le_sup_right
  have hZ'c : ∀ z ∈ Z', ∀ g ∈ H, z * g = g * z := fun z hz g hg =>
    (Subgroup.mem_centralizer_iff.1 hz.2 g hg.1).symm
  have hq : ∀ g ∈ H, ∃ n : ℕ, g ^ (2 ^ n) ∈ Z' := by
    intro g hg
    obtain ⟨hgS, hgTZ⟩ := hg
    have hgTZ' : g ∈ ((T₁ ⊔ Z : Subgroup Ω) : Set Ω) := hgTZ
    rw [Subgroup.mul_normal] at hgTZ'
    obtain ⟨t, ht, z, hz, rfl⟩ := Set.mem_mul.1 hgTZ'
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT₁2
    refine ⟨n, S.pow_mem hgS _, ?_⟩
    have ht1 : t ^ (2 ^ n) = 1 := by
      have h1 := pow_card_eq_one' (G := ↥T₁) (x := ⟨t, ht⟩)
      rw [hn] at h1
      exact congrArg Subtype.val h1
    show (t * z) ^ (2 ^ n) ∈ Z
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff z).2 hz, mul_one, ← QuotientGroup.mk_pow, ht1, QuotientGroup.mk_one]
  obtain ⟨T₀, hT₀H, hT₀2, hHT₀, hNT₀⟩ := S12.exists_char_sylow_two hZ'H hZ'c hq
  have hBH : B ≤ Subgroup.normalizer (H : Set Ω) := fun c hc =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hSN c, mem_normalizer_sup_of_mem (hBT₁ hc) ((Subgroup.normalizer_eq_top_iff.2 hZn) ▸ Subgroup.mem_top c)⟩
  refine ⟨T₀, hT₀H.trans inf_le_left, hT₀2, fun c hc => hNT₀ c (hBH hc), ?_⟩
  intro hbot
  have hcT₀ : ∀ s ∈ T₀, ∀ c ∈ B, s * c = c * s := fun s hs c hc => by
    have h1 : ⁅s, c⁆ ∈ (⁅T₀, B⁆ : Subgroup Ω) := Subgroup.commutator_mem_commutator hs hc
    rw [hbot, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm).1 h1
  have hT₁B : (⁅T₁, B⁆ : Subgroup Ω) ≤ Z := by
    rw [Subgroup.commutator_le]
    intro t ht c hc
    have htSZ : t ∈ ((S ⊔ Z : Subgroup Ω) : Set Ω) := hT₁SZ ht
    rw [Subgroup.mul_normal] at htSZ
    obtain ⟨s, hs, z, hz, rfl⟩ := Set.mem_mul.1 htSZ
    have hsH : s ∈ H := by
      refine ⟨hs, ?_⟩
      have e : s = (s * z) * z⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right (Z.inv_mem hz))
    have hsT : s ∈ ((T₀ ⊔ Z' : Subgroup Ω) : Set Ω) := hHT₀ hsH
    rw [Subgroup.mul_normal] at hsT
    obtain ⟨s₀, hs₀, z', hz', rfl⟩ := Set.mem_mul.1 hsT
    have hcs : s₀⁻¹ * c⁻¹ = c⁻¹ * s₀⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hcT₀ s₀ hs₀ c hc]
    have hw : z' * z ∈ Z := Z.mul_mem hz'.2 hz
    have e : ⁅s₀ * z' * z, c⁆ = s₀ * (⁅z' * z, c⁆) * s₀⁻¹ := by
      calc ⁅s₀ * z' * z, c⁆ = s₀ * (z' * z) * c * (z' * z)⁻¹ * (s₀⁻¹ * c⁻¹) := by
            simp only [commutatorElement_def]; group
        _ = s₀ * (z' * z) * c * (z' * z)⁻¹ * (c⁻¹ * s₀⁻¹) := by rw [hcs]
        _ = s₀ * (⁅z' * z, c⁆) * s₀⁻¹ := by simp only [commutatorElement_def]; group
    have hwc : ⁅z' * z, c⁆ ∈ Z := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      exact Z.mul_mem hw (by rw [← mul_assoc]; exact hZn.conj_mem _ (Z.inv_mem hw) c)
    rw [e]
    exact hZn.conj_mem _ hwc s₀
  rw [hT₁def, commutator_commutator_eq_of_isPGroup Nat.prime_three hBp hT (by norm_num) hBT] at hT₁B
  obtain ⟨t, ht, c, hc, hnot⟩ := hnc
  apply hnot
  have h1 : ⁅t, c⁆ ∈ Z := hT₁B (Subgroup.commutator_mem_commutator ht hc)
  exact centMod_iff.1 (centMod_of_mem_centralizer h1)

theorem false_of_qs_case1 {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K)
    (hc : catalogIs (PSimple 3 K) S9.isTE6two)
    (hmax : ∀ E : Subgroup Ω, IsElemAbelian 3 E → E ≤ S ⊔ B → Nat.card E ≤ Nat.card B) : False := by
  have hcfg := h.cfg
  have h3K : 3 ∣ Nat.card K := by
    have h1 := card_pSimple_dvd 3 K
    rw [card_of_isTE6two hc] at h1
    exact (by norm_num : 3 ∣ 76532479683774853939200).trans h1
  have hact := h.nlAct h3K
  obtain ⟨hDB, -, hDcard, -, -, -, hDK⟩ := hcfg.std
  have hDL : D ≤ Subgroup.centralizer (K : Set Ω) := hDK.le.trans inf_le_right
  have hKS : K ≤ S := hact.comp.1.trans inf_le_left
  have hmaxK : IsMaxRankIn 3 B (K ⊔ B) := fun E hE hEel =>
    hmax E hEel (hE.trans (sup_le_sup_right hKS B))
  exact false_of_case1_lie hcfg.kgroup hcfg.elem hcfg.big hDB hDL hDcard hact.comp hact.norm hmaxK
    (Or.inr hc) h.nl

private theorem center_eq_bot_of_simple_three {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (h3 : 3 ∣ Nat.card X) (hne : Nat.card X ≠ 3) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := fun a b => by
      have ha : a ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp ha) b).symm
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3
    have hnorm : (Subgroup.zpowers x).Normal :=
      ⟨fun a _ g => by rwa [hcomm g a, mul_inv_cancel_right]⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h' | h'
    · rw [Subgroup.zpowers_eq_bot] at h'
      rw [h', orderOf_one] at hx
      omega
    · apply hne
      rw [← hx, ← Nat.card_zpowers, h', Subgroup.card_top]

theorem card_le_of_elemAbelian_mulAut_td42 {Q : Type} [Group Q] [Finite Q]
    (hQ : catalogIs Q S9.isTD4two) (A : Subgroup (MulAut Q)) (hA : IsElemAbelian 3 A) :
    Nat.card A ≤ 3 ^ 3 := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := CatB.lieIndex_isTD4two hQ
  obtain ⟨hq2, hq1⟩ := HDesc.pp_eq_of_card Nat.prime_two one_ne_zero
    (hq.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
  haveI : IsSimpleGroup Q := by
    haveI := (CFSG.Assembly.lie_finite_simple ⟨.trialityD4 q, hv⟩).2
    exact MulEquiv.isSimpleGroup e
  have hcardQ : Nat.card Q = 211341312 := card_fTD42 hQ
  have hcardA : Nat.card (MulAut Q) = 3 * 211341312 := card_mulAut_fTD42 hQ
  have hZ : Subgroup.center Q = ⊥ :=
    center_eq_bot_of_simple_three (by rw [hcardQ]; norm_num) (by rw [hcardQ]; norm_num)
  have hinj := mulAutConj_injective_of_center_eq_bot hZ
  set I : Subgroup (MulAut Q) := (MulAut.conj : Q →* MulAut Q).range with hIdef
  have hIc : Nat.card I = 211341312 := by
    rw [hIdef, ← hcardQ]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx : I.index = 3 := by
    have h1 := I.card_mul_index
    rw [hIc, hcardA] at h1
    omega
  have h9 : Nat.card ↥(I ⊓ A) ≤ 3 ^ 2 := by
    set F : Subgroup Q := (I ⊓ A).comap (MulAut.conj : Q →* MulAut Q) with hFdef
    have hF : IsElemAbelian 3 F :=
      isElemAbelian_comap_of_injective _ hinj (isElemAbelian_mono hA inf_le_right)
    have hFc : Nat.card F = Nat.card ↥(I ⊓ A) := by
      have h1 : F.map (MulAut.conj : Q →* MulAut Q) = I ⊓ A := Subgroup.map_comap_eq_self inf_le_left
      rw [← h1, Subgroup.card_map_of_injective hinj]
    rw [← hFc]
    exact CFSG.AGLEmbedding.d4TwoRankTwo Q ⟨.trialityD4 q, hv⟩ q hq2 hq1 rfl ⟨e⟩ F hF
  have hrel : I.relIndex A ≤ 3 := by
    have h1 := Subgroup.relIndex_le_of_le_right (H := I) (le_top : A ≤ ⊤)
      (by rw [Subgroup.relIndex_top_right, hidx]; norm_num)
    rwa [Subgroup.relIndex_top_right, hidx] at h1
  have h2 := Subgroup.relIndex_mul_card (H := I) (K := A)
  calc Nat.card A = I.relIndex A * Nat.card ↥(I ⊓ A) := h2.symm
    _ ≤ 3 * 3 ^ 2 := Nat.mul_le_mul hrel h9
    _ = 3 ^ 3 := by norm_num

private theorem exists_big_elem_abelian_six {S E₀ : Subgroup Ω} {x : Ω}
    (hE₀S : E₀ ≤ S) (hE₀ : IsElemAbelian 3 E₀) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxc : ∀ g : Ω, g * x = x * g)
    (hE : 3 ^ 5 * Nat.card ↥(E₀ ⊓ Subgroup.centralizer (S : Set Ω)) ≤ Nat.card E₀) :
    ∃ E : Subgroup Ω, IsElemAbelian 3 E ∧ E ≤ S ⊔ Subgroup.zpowers x ∧ 3 ^ 6 ≤ Nat.card E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxz : x ∈ Subgroup.center Ω := Subgroup.mem_center_iff.2 hxc
  have hCz : Subgroup.zpowers x ≤ Subgroup.center Ω := Subgroup.zpowers_le.2 hxz
  have hCN : Subgroup.zpowers x ≤ Subgroup.normalizer (E₀ : Set Ω) :=
    hCz.trans (Subgroup.center_le_normalizer _)
  have hCS : Subgroup.zpowers x ≤ Subgroup.centralizer (S : Set Ω) :=
    hCz.trans (Subgroup.center_le_centralizer _)
  have hC3 : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hcomm : ∀ a ∈ E₀, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := fun a _ b hb =>
    (Subgroup.mem_center_iff.1 (hCz hb) a)
  refine ⟨E₀ ⊔ Subgroup.zpowers x,
    IsElemAbelian.sup_of_commute hE₀ (isElemAbelian_zpowers hx3) hcomm,
    sup_le_sup_right hE₀S _, ?_⟩
  have h2 := card_sup_mul_card_inf_of_le_normalizer hCN
  rw [hC3] at h2
  have h3 : Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) ≤
      Nat.card ↥(E₀ ⊓ Subgroup.centralizer (S : Set Ω)) :=
    Subgroup.card_le_of_le (inf_le_inf_left E₀ hCS)
  have hz : 0 < Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) := Nat.card_pos
  have h4 : 3 ^ 6 * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) ≤
      Nat.card ↥(E₀ ⊔ Subgroup.zpowers x) * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) := by
    calc 3 ^ 6 * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x)
        = 3 * (3 ^ 5 * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x)) := by ring
      _ ≤ 3 * (3 ^ 5 * Nat.card ↥(E₀ ⊓ Subgroup.centralizer (S : Set Ω))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      _ ≤ 3 * Nat.card E₀ := Nat.mul_le_mul_left _ hE
      _ = Nat.card ↥(E₀ ⊔ Subgroup.zpowers x) * Nat.card ↥(E₀ ⊓ Subgroup.zpowers x) := by
        rw [h2, mul_comm]
  exact Nat.le_of_mul_le_mul_right h4 hz

theorem false_of_qs_td4_case1 {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K)
    (hK : catalogIs (PSimple 3 K) S9.isTD4two) (hS : catalogIs (PSimple 3 S) S9.isTE6two)
    (hmax : ∀ E : Subgroup Ω, IsElemAbelian 3 E → E ≤ S ⊔ B → Nat.card E ≤ Nat.card B) : False := by
  have hcfg := h.cfg
  have hbig : 3 ^ 6 ≤ Nat.card B := by
    obtain ⟨i, hi, ⟨θ⟩⟩ := hS
    cases i with
    | lie d =>
      obtain ⟨idx, hv⟩ := d
      cases idx with
      | twistedE6 q =>
        simp only [S9.isTE6two, onLie] at hi
        obtain ⟨hq2, hq1⟩ := HDesc.pp_eq_of_card Nat.prime_two one_ne_zero
          (hi.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
        obtain ⟨E₀, hE₀S, hE₀, hE₀c⟩ :=
          S171.extremalRank_twE6 hcfg.quasi hq2 (by rw [hq1]; exact odd_one) θ
        obtain ⟨E, hE, hEle, hE6⟩ := exists_big_elem_abelian_six hE₀S hE₀ (hcfg.elem.2 x hcfg.xB) hcfg.x1
          hcfg.xcen hE₀c
        exact hE6.trans (hmax E hE (hEle.trans (sup_le_sup_left (Subgroup.zpowers_le.2 hcfg.xB) S)))
      | _ => simp [S9.isTE6two, onLie] at hi
    | _ => exact hi.elim
  have h3K : 3 ∣ Nat.card K := by
    have h1 := card_pSimple_dvd 3 K
    rw [card_fTD42 hK] at h1
    exact (by norm_num : 3 ∣ 211341312).trans h1
  have hact := h.nlAct h3K
  obtain ⟨-, -, hDcard, -, -, -, -⟩ := hcfg.std
  let φ : ↥B →* MulAut (PSimple 3 K) := (chevAut 3 K).comp (Subgroup.inclusion hact.norm)
  have hker : Nat.card φ.ker ≤ Nat.card D := by
    let ι : ↥φ.ker → ↥D := fun k =>
      ⟨((k : ↥B) : Ω), (hact.ker _ (k : ↥B).2 (hact.norm (k : ↥B).2)).1 (MonoidHom.mem_ker.1 k.2)⟩
    exact Nat.card_le_card_of_injective ι
      (fun k l hkl => Subtype.ext (Subtype.ext (congrArg (fun w : ↥D => (w : Ω)) hkl)))
  have hrange : Nat.card φ.range ≤ 3 ^ 3 :=
    card_le_of_elemAbelian_mulAut_td42 hK φ.range (range_isElemAbelian_of_subgroup hcfg.elem φ)
  have hmul := Subgroup.card_ker_mul_card_range φ
  rw [hDcard] at hker
  have hle : Nat.card B ≤ 3 ^ 2 * 3 ^ 3 := by
    rw [← hmul]
    exact Nat.mul_le_mul hker hrange
  omega

theorem qSFamCTE6_of_C2 (h2 : QSFamCTE6C2) : QSFamCTE6 := by
  intro Ω _ _ S B T x D K hN hK hS
  have hc := hN.cfg
  rcases case1_or_case2 hc.normal hc.core hc.two hc.bnorm hc.rank (hc.maxc.imp id fun h => h.1) with
    hmax | hnc
  · exact (false_of_qs_case1 hN hK hmax).elim
  · exact h2 Ω S B T x D K hN hK hS
      (exists_two_subgroup_of_case2 hc.kgroup hc.comp hc.normal hc.core hc.chev hc.elem hc.two hc.bnorm hnc)

theorem qSFamCTD4_of_C2 (h2 : QSFamCTD4C2) : QSFamCTD4 := by
  intro Ω _ _ S B T x D K hN hK hS
  have hc := hN.cfg
  rcases case1_or_case2 hc.normal hc.core hc.two hc.bnorm hc.rank (hc.maxc.imp id fun h => h.1) with
    hmax | hnc
  · exact (false_of_qs_td4_case1 hN hK hS hmax).elim
  · exact h2 Ω S B T x D K hN hK hS
      (exists_two_subgroup_of_case2 hc.kgroup hc.comp hc.normal hc.core hc.chev hc.elem hc.two hc.bnorm hnc)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.S265C.C1

end
