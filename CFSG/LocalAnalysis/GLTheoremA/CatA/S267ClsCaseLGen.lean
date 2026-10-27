module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLU
import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL
import CFSG.CGT.T75P.SylowSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt
open scoped IsMulCommutative

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {τ : K →+* K}

section Gen

variable [Finite K] {p : ℕ} {Aε : Subgroup (GL ι K)} [IsMulCommutative Aε]
variable {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K}

private theorem zpowers_inf_eq_bot_of_not_mem (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    {x : G} (hxp : x ^ p = 1) {L : Subgroup G} (hxL : x ∉ L) :
    Subgroup.zpowers x ⊓ L = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := fun h => hxL (h ▸ L.one_mem)
  have hcard : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ L) ∣ p :=
    hcard ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · exfalso
    have heq : Subgroup.zpowers x ⊓ L = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hcard])
    have hmem : x ∈ Subgroup.zpowers x ⊓ L := by rw [heq]; exact Subgroup.mem_zpowers x
    exact hxL hmem.2

theorem biInf_sdiff_le_of_supported (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1)
    (hpK : (p : K) ≠ 0) (hAεβ : Aε ≤ isomGL β) {𝒮 : Set ((ι → K) →+ (ι → K))}
    (hmax : IsMaxElem β (glRep Aε) p 𝒮)
    (h𝒮 : ∀ s ∈ 𝒮, ∀ a v, s (glRep Aε a v) = glRep Aε a (s v))
    (h𝒮W : ∀ s ∈ 𝒮, ∀ i, ∀ v ∈ weightFamily (p := p) (glRep Aε) i,
      s v ∈ weightFamily (p := p) (glRep Aε) i)
    [DecidableEq (Hyperplane ↥Aε p)] (T : Finset (Hyperplane ↥Aε p))
    (hT : ∀ H' : Hyperplane ↥Aε p, H' ∈ T ↔ weightSpace (glRep Aε) H'.1 ≠ ⊥)
    (x : Hyperplane ↥Aε p → ↥Aε) (hx : ∀ H ∈ T, x H ∉ H.1)
    (hx' : ∀ H ∈ T, ∀ H' ∈ T, H' ≠ H → x H ∈ H'.1) {A' : Subgroup ↥Aε} :
    ∀ S ⊆ T, (∀ H ∈ S, x H ∈ A') → (⨅ H' ∈ T \ S, H'.1) ≤ A' := by
  have hρ : IsIsomRep β (glRep Aε) := isIsomRep_glRep hAεβ
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    have h1 := card_biInf_sdiff β (glRep Aε) hp hA hpK hρ hmax h𝒮 h𝒮W (glRep_injective Aε) T hT
      (Finset.empty_subset T)
    rw [Finset.card_empty, pow_zero] at h1
    rw [Subgroup.eq_bot_of_card_eq _ h1]
    exact bot_le
  | insert H S hHS ih =>
    intro hST hS
    have hHT : H ∈ T := hST (Finset.mem_insert_self H S)
    have hST' : S ⊆ T := fun H' hH' => hST (Finset.mem_insert_of_mem hH')
    have hle := ih hST' fun H' hH' => hS H' (Finset.mem_insert_of_mem hH')
    set G := ⨅ H' ∈ T \ S, H'.1 with hG
    set G' := ⨅ H' ∈ T \ insert H S, H'.1 with hG'
    have hGG' : G ≤ G' := by
      intro g hg
      rw [hG', Subgroup.mem_iInf]
      intro H'
      rw [Subgroup.mem_iInf]
      intro hH'
      have hg' := (Subgroup.mem_iInf.mp hg) H'
      rw [Subgroup.mem_iInf] at hg'
      exact hg' (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hH').1,
        fun h => (Finset.mem_sdiff.mp hH').2 (Finset.mem_insert_of_mem h)⟩)
    have hxG' : x H ∈ G' := by
      rw [hG', Subgroup.mem_iInf]
      intro H'
      rw [Subgroup.mem_iInf]
      intro hH'
      obtain ⟨hH'T, hH'S⟩ := Finset.mem_sdiff.mp hH'
      exact hx' H hHT H' hH'T fun h => hH'S (h ▸ Finset.mem_insert_self H S)
    have hHG : H ∈ T \ S := Finset.mem_sdiff.mpr ⟨hHT, hHS⟩
    have hxG : x H ∉ G := fun h => by
      have h1 := Subgroup.mem_iInf.mp h H
      rw [Subgroup.mem_iInf] at h1
      exact hx H hHT (h1 hHG)
    have hinf : G ⊓ Subgroup.zpowers (x H) = ⊥ := by
      rw [inf_comm, eq_bot_iff]
      intro g hg
      have hzx := zpowers_inf_eq_bot_of_not_mem hp (hA (x H)) (hx H hHT)
      have hgH : g ∈ H.1 := by
        have := (Subgroup.mem_iInf.mp hg.2 H)
        rw [Subgroup.mem_iInf] at this
        exact this hHG
      rw [← hzx]
      exact ⟨hg.1, hgH⟩
    have hcard : Nat.card ↥(G ⊔ Subgroup.zpowers (x H)) = Nat.card ↥G' := by
      have hcomm : ∀ a ∈ G, ∀ b ∈ Subgroup.zpowers (x H), a * b = b * a := fun a _ b _ =>
        mul_comm a b
      rw [CFSG.CGT.T75P.card_sup_of_commute hcomm hinf, hG, hG',
        card_biInf_sdiff β (glRep Aε) hp hA hpK hρ hmax h𝒮 h𝒮W (glRep_injective Aε) T hT hST',
        card_biInf_sdiff β (glRep Aε) hp hA hpK hρ hmax h𝒮 h𝒮W (glRep_injective Aε) T hT hST,
        Finset.card_insert_of_notMem hHS, pow_succ]
      haveI : Fact p.Prime := ⟨hp⟩
      have hx1 : x H ≠ 1 := fun h => hxG (h ▸ G.one_mem)
      rw [Nat.card_zpowers, orderOf_eq_prime (hA (x H)) hx1]
    have heq : G ⊔ Subgroup.zpowers (x H) = G' :=
      Subgroup.eq_of_le_of_card_ge (sup_le hGG' (Subgroup.zpowers_le.mpr hxG')) hcard.ge
    rw [← heq]
    exact sup_le hle (Subgroup.zpowers_le.mpr (hS H (Finset.mem_insert_self H S)))

theorem exists_pair_not_mem (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1)
    (hpK : (p : K) ≠ 0) (hAεβ : Aε ≤ isomGL β) {𝒮 : Set ((ι → K) →+ (ι → K))}
    (hmax : IsMaxElem β (glRep Aε) p 𝒮)
    (h𝒮 : ∀ s ∈ 𝒮, ∀ a v, s (glRep Aε a v) = glRep Aε a (s v))
    (h𝒮W : ∀ s ∈ 𝒮, ∀ i, ∀ v ∈ weightFamily (p := p) (glRep Aε) i,
      s v ∈ weightFamily (p := p) (glRep Aε) i)
    [DecidableEq (Hyperplane ↥Aε p)] (T : Finset (Hyperplane ↥Aε p))
    (hT : ∀ H' : Hyperplane ↥Aε p, H' ∈ T ↔ weightSpace (glRep Aε) H'.1 ≠ ⊥)
    (x : Hyperplane ↥Aε p → ↥Aε) (hx : ∀ H ∈ T, x H ∉ H.1)
    (hx' : ∀ H ∈ T, ∀ H' ∈ T, H' ≠ H → x H ∈ H'.1) {A' : Subgroup ↥Aε} (hA' : A' ≠ ⊤)
    {ζ : ↥Aε} (hζA : ζ ∈ A') (hζ : ∀ H ∈ T, ζ ∉ H.1) :
    ∃ Ha ∈ T, ∃ Hb ∈ T, Ha ≠ Hb ∧ x Ha ∉ A' ∧ x Hb ∉ A' := by
  by_contra hcon
  push Not at hcon
  have hgen := biInf_sdiff_le_of_supported hp hA hpK hAεβ hmax h𝒮 h𝒮W T hT x hx hx'
    (A' := A')
  by_cases hall : ∀ H ∈ T, x H ∈ A'
  · apply hA'
    have h1 := hgen T le_rfl hall
    rw [Finset.sdiff_self] at h1
    simp only [Finset.notMem_empty, iInf_false, iInf_top] at h1
    exact top_le_iff.mp h1
  · push Not at hall
    obtain ⟨H₀, hH₀T, hH₀⟩ := hall
    have hrest : ∀ H ∈ T.erase H₀, x H ∈ A' := fun H hH => by
      by_contra hxH
      exact hxH (hcon H₀ hH₀T H (Finset.mem_of_mem_erase hH) (Finset.ne_of_mem_erase hH).symm hH₀)
    have h1 := hgen (T.erase H₀) (Finset.erase_subset _ _) hrest
    rw [Finset.sdiff_erase_self hH₀T] at h1
    simp only [Finset.mem_singleton, iInf_iInf_eq_left] at h1
    have hdvd := Subgroup.index_dvd_of_le h1
    rw [H₀.2] at hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact hA' (Subgroup.index_eq_one.mp h)
    · have heq : A' = H₀.1 := by
        have hcard := Subgroup.card_mul_index A'
        have hcard₀ := Subgroup.card_mul_index H₀.1
        rw [h] at hcard
        rw [H₀.2] at hcard₀
        exact (Subgroup.eq_of_le_of_card_ge h1 (by
          have hp0 : 0 < p := hp.pos
          exact (Nat.eq_of_mul_eq_mul_right hp0 (hcard.trans hcard₀.symm)).le)).symm
      exact hζ H₀ hH₀T (heq ▸ hζA)

theorem exists_caseL_pair (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1)
    (hpK : (p : K) ≠ 0) (hAεβ : Aε ≤ isomGL β) {𝒮 : Set ((ι → K) →+ (ι → K))}
    (hmax : IsMaxElem β (glRep Aε) p 𝒮)
    (h𝒮 : ∀ s ∈ 𝒮, ∀ a v, s (glRep Aε a v) = glRep Aε a (s v))
    (h𝒮W : ∀ s ∈ 𝒮, ∀ i, ∀ v ∈ weightFamily (p := p) (glRep Aε) i,
      s v ∈ weightFamily (p := p) (glRep Aε) i)
    [DecidableEq (Hyperplane ↥Aε p)] (T : Finset (Hyperplane ↥Aε p))
    (hT : ∀ H' : Hyperplane ↥Aε p, H' ∈ T ↔ weightSpace (glRep Aε) H'.1 ≠ ⊥) (hT2 : 2 ≤ T.card)
    {A' : Subgroup ↥Aε} (hidx : Nat.card ↥Aε ≤ p * Nat.card A')
    {ζ : ↥Aε} (hζA : ζ ∈ A') (hζ : ∀ H ∈ T, ζ ∉ H.1) :
    ∃ Ha ∈ T, ∃ Hb ∈ T, Ha ≠ Hb ∧
      (∃ y ∈ A', y ∉ Ha.1 ∧ y ∉ Hb.1 ∧ ∀ H ∈ T, H ≠ Ha → H ≠ Hb → y ∈ H.1) ∧
      (A' = ⊤ ∨ ∃ g ∈ (⨅ H' ∈ T \ {Ha, Hb}, H'.1), g ∉ A') ∧
      ∀ Hm ∈ T, Hm ≠ Ha → Hm ≠ Hb → ∃ x' ∈ A', x' ∉ Hm.1 ∧
        ∀ H ∈ T, H ≠ Hm → H ≠ Ha → H ≠ Hb → x' ∈ H.1 := by
  classical
  have hρ : IsIsomRep β (glRep Aε) := isIsomRep_glRep hAεβ
  have hsupp : ∀ H : Hyperplane ↥Aε p, ∃ x : ↥Aε,
      H ∈ T → x ∉ H.1 ∧ ∀ H' ∈ T, H' ≠ H → x ∈ H'.1 := by
    intro H
    by_cases hH : H ∈ T
    · obtain ⟨x, hx, hx'⟩ := exists_supported_element β (glRep Aε) hp hA hpK hρ hmax h𝒮 h𝒮W
        {H} (fun H' hH' => by rw [Finset.mem_singleton.mp hH']; exact (hT H).mp hH)
      exact ⟨x, fun _ => ⟨hx H (Finset.mem_singleton_self H), fun H' hH'T hne =>
        hx' H' (fun h => hne (Finset.mem_singleton.mp h)) ((hT H').mp hH'T)⟩⟩
    · exact ⟨1, fun h => absurd h hH⟩
  choose x hx using hsupp
  have hxn : ∀ H ∈ T, x H ∉ H.1 := fun H hH => (hx H hH).1
  have hxs : ∀ H ∈ T, ∀ H' ∈ T, H' ≠ H → x H ∈ H'.1 := fun H hH => (hx H hH).2
  have hpow : ∀ H ∈ T, ∀ m : ℕ, x H ^ m ∈ H.1 → x H ^ m = 1 := fun H hH m hm => by
    have h0 := zpowers_inf_eq_bot_of_not_mem hp (hA (x H)) (hxn H hH)
    have : x H ^ m ∈ Subgroup.zpowers (x H) ⊓ H.1 := ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m, hm⟩
    rw [h0] at this
    exact this
  by_cases hAt : A' = ⊤
  ·
    obtain ⟨Ha, hHa, Hb, hHb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
    obtain ⟨y, hy, hy'⟩ := exists_supported_element β (glRep Aε) hp hA hpK hρ hmax h𝒮 h𝒮W
      {Ha, Hb} (fun H' hH' => by
        rcases Finset.mem_insert.mp hH' with rfl | hH'
        · exact (hT _).mp hHa
        · rw [Finset.mem_singleton.mp hH']; exact (hT _).mp hHb)
    refine ⟨Ha, hHa, Hb, hHb, hab, ⟨y, hAt ▸ Subgroup.mem_top y, hy Ha (by simp),
      hy Hb (by simp), fun H hH hna hnb => hy' H (by simp [hna, hnb]) ((hT H).mp hH)⟩,
      Or.inl hAt, fun Hm hHm hma hmb => ⟨x Hm, hAt ▸ Subgroup.mem_top _, hxn Hm hHm,
        fun H hH hm _ _ => hxs Hm hHm H hH hm⟩⟩
  · obtain ⟨Ha, hHa, Hb, hHb, hab, hxa, hxb⟩ :=
      exists_pair_not_mem hp hA hpK hAεβ hmax h𝒮 h𝒮W T hT x hxn hxs hAt hζA hζ
    have hsup : A' ⊔ Subgroup.zpowers (x Ha) = ⊤ := by
      have hel : IsElemAbelian p (⊤ : Subgroup ↥Aε) :=
        ⟨⟨⟨fun a b => mul_comm a b⟩⟩, fun a _ => hA a⟩
      have hc := card_sup_zpowers_of_not_mem hp hel le_top (Subgroup.mem_top _) hxa
      refine Subgroup.eq_top_of_card_eq _ ?_
      have hle := Subgroup.card_le_card_group (A' ⊔ Subgroup.zpowers (x Ha))
      rw [hc] at hle ⊢
      exact le_antisymm hle (by rw [mul_comm]; exact hidx)
    have hdec : ∀ g : ↥Aε, ∃ a ∈ A', ∃ m : ℕ, m < p ∧ g = a * x Ha ^ m := fun g => by
      have hel : IsElemAbelian p (⊤ : Subgroup ↥Aε) :=
        ⟨⟨⟨fun a b => mul_comm a b⟩⟩, fun a _ => hA a⟩
      exact exists_mul_pow_of_mem_sup hp hel le_top (Subgroup.mem_top _)
        (by rw [hsup]; exact Subgroup.mem_top g)
    obtain ⟨a, haA, m, -, hbm⟩ := hdec (x Hb)
    have hxaH : ∀ H ∈ T, H ≠ Ha → x Ha ^ m ∈ H.1 := fun H hH hne =>
      Subgroup.pow_mem _ (hxs Ha hHa H hH hne) m
    have hya : a = x Hb * (x Ha ^ m)⁻¹ := by rw [hbm]; group
    refine ⟨Ha, hHa, Hb, hHb, hab, ⟨a, haA, fun haH => ?_, fun haH => ?_, fun H hH hna hnb => ?_⟩,
      Or.inr ⟨x Ha, ?_, hxa⟩, fun Hm hHm hma hmb => ?_⟩
    ·
      have h1 : x Ha ^ m ∈ Ha.1 := by
        have : x Ha ^ m = a⁻¹ * x Hb := by rw [hbm]; group
        rw [this]
        exact Ha.1.mul_mem (Ha.1.inv_mem haH) (hxs Hb hHb Ha hHa hab)
      have h2 := hpow Ha hHa m h1
      rw [hya, h2, inv_one, mul_one] at haA
      exact hxb haA
    ·
      apply hxn Hb hHb
      rw [hbm]
      exact Hb.1.mul_mem haH (hxaH Hb hHb (Ne.symm hab))
    · rw [hya]
      exact H.1.mul_mem (hxs Hb hHb H hH hnb) (H.1.inv_mem (hxaH H hH hna))
    · rw [Subgroup.mem_iInf]
      intro H'
      rw [Subgroup.mem_iInf]
      intro hH'
      obtain ⟨hH'T, hH'I⟩ := Finset.mem_sdiff.mp hH'
      exact hxs Ha hHa H' hH'T fun h => hH'I (h ▸ Finset.mem_insert_self _ _)
    · obtain ⟨a', ha'A, m', -, hm⟩ := hdec (x Hm)
      refine ⟨a', ha'A, fun ha'H => hxn Hm hHm ?_, fun H hH hm' hma' hmb' => ?_⟩
      · rw [hm]
        exact Hm.1.mul_mem ha'H (Subgroup.pow_mem _ (hxs Ha hHa Hm hHm hma) m')
      · have : a' = x Hm * (x Ha ^ m')⁻¹ := by rw [hm]; group
        rw [this]
        exact H.1.mul_mem (hxs Hm hHm H hH hm') (H.1.inv_mem (Subgroup.pow_mem _
          (hxs Ha hHa H hH hma') m'))

end Gen

section SubBlock

variable [Finite K] {p : ℕ} {Aε : Subgroup (GL ι K)} [IsMulCommutative Aε]
variable {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K}

theorem glaPLayer_ne_bot_of_subBlock_supp (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1)
    (hpK : (p : K) ≠ 0) (hAεβ : Aε ≤ isomGL β) [DecidableEq (Hyperplane ↥Aε p)]
    (I : Finset (Hyperplane ↥Aε p)) {H₂ : Hyperplane ↥Aε p} (hH₂ : H₂ ∉ I) {x : ↥Aε}
    (hx₂ : x ∉ H₂.1)
    (hxU : ∀ H'' : Hyperplane ↥Aε p, H'' ∉ insert H₂ I →
      weightSpace (glRep Aε) H''.1 ≠ ⊥ → x ∈ H''.1)
    (hq : CFSG.Open.IsQuasisimple ↥(blkI β (wtU Aε (insert H₂ I)) (wtW Aε (insert H₂ I))))
    (hpJ : p ∣ Nat.card ↥(blkI β (wtU Aε (insert H₂ I)) (wtW Aε (insert H₂ I)))) :
    GLAPLayer p (blkI β (wtU Aε I) (wtW Aε I) ⊓ Subgroup.centralizer {(x : GL ι K)}) ≠ ⊥ := by
  classical
  set U := wtU Aε I with hUdef
  set W := wtW Aε I with hWdef
  set U' := wtU Aε (insert H₂ I) with hU'def
  set W' := wtW Aε (insert H₂ I) with hW'def
  set J' := blkI β U' W' with hJ'def
  set C := blkI β U W ⊓ Subgroup.centralizer {(x : GL ι K)} with hCdef
  set F := I.filter fun H => x ∉ H.1 with hFdef
  have hFI : F ⊆ I := Finset.filter_subset _ _
  have hH₂F : H₂ ∉ F := fun h => hH₂ (hFI h)
  set J := insert H₂ F with hJdef
  have hJ : ∀ H ∈ J, x ∉ H.1 := by
    intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH
    · exact hx₂
    · exact (Finset.mem_filter.mp hH).2
  have hJ' : ∀ H'' : Hyperplane ↥Aε p, H'' ∉ J → weightSpace (glRep Aε) H''.1 ≠ ⊥ →
      x ∈ H''.1 := by
    intro H'' hH'' hne
    by_cases h : H'' ∈ insert H₂ I
    · rcases Finset.mem_insert.mp h with rfl | hI
      · exact absurd (Finset.mem_insert_self _ _) hH''
      · by_contra hx
        exact hH'' (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hI, hx⟩))
    · exact hxU H'' h hne
  have hJsub : J ⊆ insert H₂ I := Finset.insert_subset_insert H₂ hFI
  have hU'W' : IsCompl U' W' := isCompl_ker_range_projI (glRep Aε) hp hA hpK (insert H₂ I)
  obtain ⟨hWW', hW₂W', hdecW'⟩ := wtW_insert hp hA hpK hH₂
  have hU'U : ∀ u ∈ U', u ∈ U := fun u hu => ((mem_wtU_insert hp hA hpK hH₂ u).mp hu).1
  have hPJ : ∀ v, projI (glRep Aε) J v = projI (glRep Aε) J (projI (glRep Aε) (insert H₂ I) v) := by
    intro v
    rw [projI_projI_eq_inter (glRep Aε) hp hA hpK, Finset.inter_eq_left.mpr hJsub]
  have hPF : ∀ v, projI (glRep Aε) F v = projI (glRep Aε) F (projI (glRep Aε) I v) := by
    intro v
    rw [projI_projI_eq_inter (glRep Aε) hp hA hpK, Finset.inter_eq_left.mpr hFI]
  have hPJsplit : ∀ v, projI (glRep Aε) J v =
      projI (glRep Aε) {H₂} v + projI (glRep Aε) F v := by
    intro v
    rw [projI_apply, Finset.sum_insert hH₂F, projI_apply, projI_apply, Finset.sum_singleton]
  have hxfix : ∀ v ∈ U', glEquiv (x : GL ι K) v = v := fun v hv => by
    rw [← glRep_apply_eq_glEquiv]
    refine (apply_eq_self_iff_projI (glRep Aε) hp hA hpK hJ hJ' v).mpr ?_
    rw [hPJ, show projI (glRep Aε) (insert H₂ I) v = 0 from hv, map_zero]
  have hxW' : ∀ w ∈ W', glEquiv (x : GL ι K) w ∈ W' := fun w hw => by
    have := (preserves_wtU_wtW hp hA hpK (insert H₂ I) _ (glRep_preserves_weightFamily x)).2 w hw
    simpa only [LinearMap.toAddMonoidHom_coe, glRep_apply_eq_glEquiv] using this
  have hsub : blkSub β U' W' ≤ blkSub β U W := by
    rintro g ⟨hgβ, hgU, hgW⟩
    refine ⟨hgβ, fun u hu => ?_, fun w hw => hgW w (hWW' hw)⟩
    obtain ⟨u', hu', w', hw', rfl⟩ := Submodule.mem_sup.1
      (show u ∈ U' ⊔ W' by rw [hU'W'.sup_eq_top]; trivial)
    have hw'U : w' ∈ U := by
      have h1 : u' + w' - u' = w' := by abel
      rw [← h1]
      exact U.sub_mem hu (hU'U u' hu')
    rw [map_add, hgW w' hw']
    exact U.add_mem (hU'U _ (hgU u' hu')) hw'U
  have hcent : blkSub β U' W' ≤ Subgroup.centralizer {(x : GL ι K)} := by
    rintro g ⟨-, hgU, hgW⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply glEquiv.injective
    refine linearEquiv_ext_of_isCompl hU'W' (fun u hu => ?_) fun w hw => ?_
    · rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxfix u hu,
        hxfix _ (hgU u hu)]
    · rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgW w hw,
        hgW _ (hxW' w hw)]
  have hJ'C : J' ≤ C := by
    refine le_inf ?_ ((blkI_le_blkSub β U' W').trans hcent)
    exact Subgroup.commutator_mono hsub hsub
  have hnorm : ∀ g ∈ C, ∀ f ∈ J', g * f * g⁻¹ ∈ J' := by
    rintro g ⟨hgI, hgx⟩ f hf
    obtain ⟨hgβ, hgU, hgW⟩ := blkI_le_blkSub β U W hgI
    have hgx' : ∀ v, (glEquiv g : (ι → K) →ₗ[K] (ι → K)) (glRep Aε x v) =
        glRep Aε x (glEquiv g v) := by
      intro v
      have hgx2 : g * (x : GL ι K) = x * g := Subgroup.mem_centralizer_singleton_iff.mp hgx
      simp only [glRep_apply_eq_glEquiv, LinearEquiv.coe_coe]
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, hgx2]
    obtain ⟨hgJU, hgJW⟩ := preserves_of_comm_supported (glRep Aε) hp hA hpK hJ hJ' _ hgx'
    have hFU : ∀ v ∈ U, projI (glRep Aε) F v = 0 := fun v hv => by
      rw [hPF, show projI (glRep Aε) I v = 0 from hv, map_zero]
    refine conj_mem_blkI hgβ (fun u hu => ?_) (fun w hw => ?_) hf
    · have hgu : glEquiv g u ∈ U := hgU u (hU'U u hu)
      have hJu : projI (glRep Aε) J (glEquiv g u) = 0 := by
        have hu' : u ∈ LinearMap.ker (projI (glRep Aε) J) := by
          show projI (glRep Aε) J u = 0
          rw [hPJ, show projI (glRep Aε) (insert H₂ I) u = 0 from hu, map_zero]
        exact hgJU u hu'
      refine (mem_wtU_insert hp hA hpK hH₂ _).mpr ⟨hgu, ?_⟩
      show projI (glRep Aε) {H₂} (glEquiv g u) = 0
      rw [hPJsplit, hFU _ hgu, add_zero] at hJu
      exact hJu
    · rw [hdecW' w hw, map_add, hgW _ ⟨w, rfl⟩]
      refine W'.add_mem (hWW' ⟨w, rfl⟩) ?_
      set w₂ := projI (glRep Aε) {H₂} w with hw₂
      have hw₂U : w₂ ∈ U := weightSpace_le_ker_projI hp hA hpK hH₂ (by
        rw [hw₂, projI_apply, Finset.sum_singleton]
        exact ⟨w, rfl⟩)
      have hw₂J : w₂ ∈ LinearMap.range (projI (glRep Aε) J) := by
        refine ⟨w₂, ?_⟩
        rw [hPJsplit, hFU _ hw₂U, add_zero, hw₂, projI_projI (glRep Aε) hp hA hpK]
      obtain ⟨v, hv⟩ := hgJW w₂ hw₂J
      have hgw₂U : glEquiv g w₂ ∈ U := hgU w₂ hw₂U
      have hgw₂ : glEquiv g w₂ = projI (glRep Aε) {H₂} (glEquiv g w₂) := by
        have hv' : projI (glRep Aε) J v = glEquiv g w₂ := hv
        have h1 : projI (glRep Aε) J (glEquiv g w₂) = glEquiv g w₂ := by
          rw [← hv', projI_projI (glRep Aε) hp hA hpK]
        rw [hPJsplit, hFU _ hgw₂U, add_zero] at h1
        exact h1.symm
      rw [hgw₂]
      exact hW₂W' ⟨_, rfl⟩
  have hn : (J'.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm g g.2 n hn⟩
  have hcomp := CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp hq hpJ hJ'C hn
  intro hbot
  have hle : J' ≤ GLAPLayer p C := le_sSup hcomp
  rw [hbot, le_bot_iff] at hle
  rw [hle, Subgroup.card_bot] at hpJ
  exact hp.one_lt.ne' (Nat.dvd_one.mp hpJ)

end SubBlock

section Semi

variable [Finite K]

theorem semiMap_preserves_of_semiConj (A : GL ι K) (σ : K ≃+* K) {y : GL ι K} {c : Kˣ}
    (hconj : ModelGen.semiConj A σ y = Matrix.GeneralLinearGroup.scalar ι c * y)
    {U W : Submodule K (ι → K)} (hUW : IsCompl U W) (hyU : ∀ u ∈ U, glEquiv y u = u)
    (hyW : ∀ w ∈ W, glEquiv y w ∈ W) (hyW' : ∀ w ∈ W, glEquiv y w = w → w = 0)
    (hdim : Module.finrank K W < Module.finrank K U) :
    (∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) ∧ ∀ w ∈ W, ModelGen.semiMap A σ w ∈ W := by
  set a := ModelGen.semiMap A σ with ha
  have hay : ∀ v, a (glEquiv y v) = (c : K) • glEquiv y (a v) := by
    intro v
    have h := ModelGen.glEquiv_semiConj_apply A σ y v
    rw [hconj, map_mul, LinearEquiv.mul_apply, glEquiv_scalar_apply] at h
    exact h.symm
  have hfixU : ∀ v, glEquiv y v = v → v ∈ U := by
    intro v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1
      (show v ∈ U ⊔ W by rw [hUW.sup_eq_top]; trivial)
    rw [map_add, hyU u hu] at hv
    have hw' : glEquiv y w = w := add_left_cancel hv
    rw [hyW' w hw hw', add_zero]
    exact hu
  have heigW : ∀ (μ : K), μ ≠ 1 → ∀ v, glEquiv y v = μ • v → v ∈ W := by
    intro μ hμ v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1
      (show v ∈ U ⊔ W by rw [hUW.sup_eq_top]; trivial)
    rw [map_add, hyU u hu, smul_add] at hv
    have h1 : u - μ • u = μ • w - glEquiv y w := by
      rw [sub_eq_sub_iff_add_eq_add]
      calc u + glEquiv y w = μ • u + μ • w := hv
        _ = μ • w + μ • u := add_comm _ _
    have hmemU : u - μ • u ∈ U := U.sub_mem hu (U.smul_mem μ hu)
    have hmemW : u - μ • u ∈ W := h1 ▸ W.sub_mem (W.smul_mem μ hw) (hyW w hw)
    have h0 : u - μ • u = 0 := by
      have := hUW.inf_eq_bot
      rw [eq_bot_iff] at this
      exact (Submodule.mem_bot K).mp (this ⟨hmemU, hmemW⟩)
    have hu0 : u = 0 := by
      have h2 : ((1 : K) - μ) • u = 0 := by rw [sub_smul, one_smul]; exact h0
      exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hμ))
    rw [hu0, zero_add]
    exact hw
  by_cases hc1 : (c : K) = 1
  ·
    have hcomm : ∀ v, a (glEquiv y v) = glEquiv y (a v) := fun v => by
      rw [hay, hc1, one_smul]
    refine ⟨fun u hu => hfixU _ ?_, fun w hw => ?_⟩
    · have h1 := hcomm u
      rw [hyU u hu] at h1
      exact h1.symm
    have hT : ∀ w ∈ W, (glEquiv y : (ι → K) →ₗ[K] (ι → K)) w - w ∈ W := fun w hw =>
      W.sub_mem (hyW w hw) hw
    let T : W →ₗ[K] W := ((glEquiv y : (ι → K) →ₗ[K] (ι → K)) - LinearMap.id).restrict hT
    have hTinj : Function.Injective T := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨w', hw'⟩ h0
      have h1 := congrArg Subtype.val h0
      simp only [T, LinearMap.restrict_coe_apply, LinearMap.sub_apply, LinearMap.id_apply,
        ZeroMemClass.coe_zero, LinearEquiv.coe_coe] at h1
      exact Subtype.ext (hyW' w' hw' (sub_eq_zero.mp h1))
    obtain ⟨⟨w₁, hw₁⟩, hTw₁⟩ := (LinearMap.injective_iff_surjective.mp hTinj) ⟨w, hw⟩
    have hw₁e : w = glEquiv y w₁ - w₁ := by
      have h1 := congrArg Subtype.val hTw₁
      simp only [T, LinearMap.restrict_coe_apply, LinearMap.sub_apply, LinearMap.id_apply,
        LinearEquiv.coe_coe] at h1
      exact h1.symm
    rw [hw₁e, map_sub, hcomm]
    obtain ⟨u, hu, w', hw', huw⟩ := Submodule.mem_sup.1
      (show a w₁ ∈ U ⊔ W by rw [hUW.sup_eq_top]; trivial)
    rw [← huw, map_add, hyU u hu, add_sub_add_left_eq_sub]
    exact W.sub_mem (hyW w' hw') hw'
  ·
    exfalso
    have hc0 : (c : K) ≠ 0 := Units.ne_zero c
    have haU : ∀ u ∈ U, a u ∈ W := by
      intro u hu
      refine heigW (c : K)⁻¹ (fun h => hc1 (inv_eq_one.mp h)) _ ?_
      have h1 := hay u
      rw [hyU u hu] at h1
      have h2 : (c : K)⁻¹ • a u = glEquiv y (a u) := by
        conv_lhs => rw [h1]
        rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      exact h2.symm
    let b := Module.finBasis K U
    have hli : LinearIndependent K (fun i => ((b i : U) : ι → K)) :=
      b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
    have hli' : LinearIndependent K (a.toAddMonoidHom ∘ fun i => ((b i : U) : ι → K)) :=
      hli.map_of_injective_injective σ.symm a.toAddMonoidHom
        (fun r hr => by simpa using hr) (fun m hm => by simpa using hm)
        (fun r m => by
          show a (σ.symm r • m) = r • a m
          rw [ha, ModelGen.semiMap_smul, RingEquiv.apply_symm_apply])
    have hli'' : LinearIndependent K (fun i => (⟨a (b i), haU _ (b i).2⟩ : W)) := by
      apply LinearIndependent.of_comp W.subtype
      exact hli'
    have := hli''.fintype_card_le_finrank
    rw [Fintype.card_fin] at this
    omega

end Semi

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
