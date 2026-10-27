
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedBasic
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin

structure Alt2Struct {G : Type*} [Group G] (K E : Subgroup G) (m : ℕ) : Prop where
  le : E ≤ K
  elem : IsElemAbelian 2 E
  card : Nat.card E = 2 ^ 4
  hom : ∃ α : ↥K →* alternatingGroup (Fin m), Function.Surjective α ∧
    α.ker = E.subgroupOf K
  noncentral : ∃ k ∈ K, ∃ e ∈ E, k * e ≠ e * k

section Basic

variable {G : Type*} [Group G] {K E : Subgroup G} {m : ℕ}

theorem Alt2Struct.isPGroup (h : Alt2Struct K E m) : IsPGroup 2 E := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have := h.elem.2 (x : G) x.2
  simpa using this

theorem Alt2Struct.normal (h : Alt2Struct K E m) : (E.subgroupOf K).Normal := by
  obtain ⟨α, -, hker⟩ := h.hom
  rw [← hker]
  exact α.normal_ker

end Basic

section Simple

theorem isSubnormal_of_simple {A : Type*} [Group A] [IsSimpleGroup A] {H K : Subgroup A}
    (h : IsSubnormal H K) (hK : K = ⊥ ∨ K = ⊤) : H = ⊥ ∨ H = ⊤ :=
  by
    rcases hK with rfl | rfl
    · exact Or.inl (le_bot_iff.1 h.le)
    · exact h.eq_bot_or_top

end Simple

section Core

variable {G : Type} [Group G] [Finite G] {K E : Subgroup G} {m : ℕ}

theorem Alt2Struct.pCore_le (h : Alt2Struct K E m) (hs : IsSimpleGroup (alternatingGroup (Fin m)))
    (hn : ¬ IsPGroup 2 (alternatingGroup (Fin m))) :
    CFSG.Open.pCore 2 ↥K ≤ E.subgroupOf K := by
  obtain ⟨α, hα, hker⟩ := h.hom
  have hnorm : ((CFSG.Open.pCore 2 ↥K).map α).Normal :=
    Subgroup.Normal.map (CFSG.LieType.BorelTits.pCore_normal 2) α hα
  have hp2 : IsPGroup 2 ((CFSG.Open.pCore 2 ↥K).map α) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥K)).map α
  have hbot : (CFSG.Open.pCore 2 ↥K).map α = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal ((CFSG.Open.pCore 2 ↥K).map α) with hb | ht
    · exact hb
    · exfalso
      apply hn
      intro x
      obtain ⟨k, hk⟩ := hp2 ⟨x, by rw [ht]; trivial⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  rw [← hker]
  intro x hx
  rw [MonoidHom.mem_ker]
  have : α x ∈ (CFSG.Open.pCore 2 ↥K).map α := ⟨x, hx, rfl⟩
  rw [hbot] at this
  exact this

theorem Alt2Struct.pCoreOf_eq (h : Alt2Struct K E m)
    (hs : IsSimpleGroup (alternatingGroup (Fin m)))
    (hn : ¬ IsPGroup 2 (alternatingGroup (Fin m))) : pCoreOf 2 K = E := by
  refine le_antisymm ?_
    (CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 E K h.le h.normal h.isPGroup)
  calc pCoreOf 2 K = (CFSG.Open.pCore 2 ↥K).map K.subtype := rfl
    _ ≤ (E.subgroupOf K).map K.subtype := Subgroup.map_mono (h.pCore_le hs hn)
    _ = E := Subgroup.map_subgroupOf_eq_of_le h.le

omit [Finite G] in
theorem Alt2Struct.centralizer_le (h : Alt2Struct K E m)
    (hs : IsSimpleGroup (alternatingGroup (Fin m))) :
    K ⊓ Subgroup.centralizer (E : Set G) ≤ E := by
  obtain ⟨α, hα, hker⟩ := h.hom
  set C : Subgroup G := K ⊓ Subgroup.centralizer (E : Set G) with hC
  have hEn := h.normal
  have hCn : (C.subgroupOf K).Normal := by
    refine ⟨fun x hx k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨(k * x * k⁻¹).2, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
    have hx' := Subgroup.mem_centralizer_iff.1 hx.2
    have he' : (k⁻¹ * ⟨e, h.le he⟩ * k⁻¹⁻¹ : ↥K) ∈ E.subgroupOf K :=
      hEn.conj_mem _ (Subgroup.mem_subgroupOf.2 he) k⁻¹
    rw [Subgroup.mem_subgroupOf] at he'
    have h1 := hx' _ he'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at h1 ⊢
    calc e * ((k : G) * x * (k : G)⁻¹) = (k : G) * (((k : G)⁻¹ * e * (k : G)) * x) * (k : G)⁻¹ := by
          group
      _ = (k : G) * (x * ((k : G)⁻¹ * e * (k : G))) * (k : G)⁻¹ := by rw [h1]
      _ = ((k : G) * x * (k : G)⁻¹) * e := by group
  have hnorm : ((C.subgroupOf K).map α).Normal := Subgroup.Normal.map hCn α hα
  rcases hs.eq_bot_or_eq_top_of_normal ((C.subgroupOf K).map α) with hb | ht
  · intro c hc
    have hcK : c ∈ K := hc.1
    have : α ⟨c, hcK⟩ ∈ (C.subgroupOf K).map α := ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.2 hc, rfl⟩
    rw [hb] at this
    have h2 : (⟨c, hcK⟩ : ↥K) ∈ α.ker := this
    rw [hker, Subgroup.mem_subgroupOf] at h2
    exact h2
  · exfalso
    obtain ⟨k₀, hk₀, e₀, he₀, hne⟩ := h.noncentral
    have : α ⟨k₀, hk₀⟩ ∈ (C.subgroupOf K).map α := by rw [ht]; trivial
    obtain ⟨c, hc, hcα⟩ := this
    have h3 : c⁻¹ * ⟨k₀, hk₀⟩ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcα, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at h3
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
    have hcC := (Subgroup.mem_subgroupOf.1 hc).2
    have hcomm := Subgroup.mem_centralizer_iff.1 hcC
    have hEc := h.elem.1
    apply hne
    have hk : k₀ = (c : G) * ((c : G)⁻¹ * k₀) := by group
    rw [hk]
    have h4 : e₀ * ((c : G)⁻¹ * k₀) = ((c : G)⁻¹ * k₀) * e₀ :=
      congrArg Subtype.val (hEc.is_comm.comm ⟨e₀, he₀⟩ ⟨_, h3⟩)
    calc (c : G) * ((c : G)⁻¹ * k₀) * e₀ = (c : G) * (((c : G)⁻¹ * k₀) * e₀) := by group
      _ = (c : G) * (e₀ * ((c : G)⁻¹ * k₀)) := by rw [h4]
      _ = ((c : G) * e₀) * ((c : G)⁻¹ * k₀) := by group
      _ = (e₀ * (c : G)) * ((c : G)⁻¹ * k₀) := by rw [hcomm e₀ he₀]
      _ = e₀ * ((c : G) * ((c : G)⁻¹ * k₀)) := by group

theorem Alt2Struct.charTwo (h : Alt2Struct K E m)
    (hs : IsSimpleGroup (alternatingGroup (Fin m)))
    (hn : ¬ IsPGroup 2 (alternatingGroup (Fin m))) : CharTwo K := by
  unfold CharTwo
  rw [h.pCoreOf_eq hs hn]
  exact h.centralizer_le hs

omit [Finite G] in
theorem Alt2Struct.isAltOver (h : Alt2Struct K E m) : IsAltOverElemAbelian K 4 m := by
  obtain ⟨α, hα, hker⟩ := h.hom
  exact ⟨E, α, h.le, h.elem, h.card, hα, hker⟩

end Core

section Block

variable {G : Type} [Group G] {K E : Subgroup G} {m : ℕ}

theorem card_quotient_of_chi0Type {B : Subgroup G}
    (h : (∃ n : ℕ, 1 < n ∧ IsLin2Type B n) ∨ IsAltType B 3 ∨ IsAltType B 5) :
    Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 3 ∨ Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 60 ∨
      ∃ n : ℕ, 2 ≤ n ∧ Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 2 ^ n * (4 ^ n - 1) := by
  rcases h with ⟨n, hn, F, _, _, hF, α, hα, hker, -⟩ | ⟨α, hα, hker, -⟩ | ⟨α, hα, hker, -⟩
  · right
    right
    refine ⟨n, hn, ?_⟩
    have hq : ↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    have hfin : Finite F := Finite.of_fintype F
    rw [Nat.card_congr hq.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm n 2, pow_mul]
    norm_num
  · left
    have hq : ↥B ⧸ CFSG.pCore 2 ↥B ≃* alternatingGroup (Fin 3) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    rw [Nat.card_congr hq.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  · right
    left
    have hq : ↥B ⧸ CFSG.pCore 2 ↥B ≃* alternatingGroup (Fin 5) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    rw [Nat.card_congr hq.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]

theorem Alt2Struct.quotient_card (h : Alt2Struct K E m)
    (hs : IsSimpleGroup (alternatingGroup (Fin m))) {B : Subgroup G} (hBK : B ≤ K)
    (hsub : (B.subgroupOf K).IsSubnormal) :
    Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 1 ∨
      Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = Nat.card (alternatingGroup (Fin m)) := by
  obtain ⟨α, hα, hker⟩ := h.hom
  have h1 : IsSubnormal ((B.subgroupOf K).map α) ⊤ := by
    have := A3.subnormal_map α (A3.subnormal_top_iff.mpr hsub)
    rwa [Subgroup.map_top, MonoidHom.range_eq_top.mpr hα] at this
  have hmemE : ∀ b : ↥B, α ⟨b, hBK b.2⟩ = 1 → (b : G) ∈ E := by
    intro b hb
    have : (⟨b, hBK b.2⟩ : ↥K) ∈ α.ker := hb
    rw [hker, Subgroup.mem_subgroupOf] at this
    exact this
  rcases isSubnormal_of_simple h1 (Or.inr rfl) with hbot | htop
  ·
    left
    have hB2 : IsPGroup 2 ↥B := by
      intro b
      refine ⟨1, ?_⟩
      have hb1 : α ⟨b, hBK b.2⟩ = 1 := by
        have : α ⟨b, hBK b.2⟩ ∈ (B.subgroupOf K).map α :=
          ⟨⟨b, hBK b.2⟩, Subgroup.mem_subgroupOf.2 b.2, rfl⟩
        rw [hbot] at this
        exact this
      apply Subtype.ext
      have := h.elem.2 _ (hmemE b hb1)
      simpa using this
    have htop' : CFSG.pCore 2 ↥B = ⊤ := by
      refine top_le_iff.mp (le_sSup ⟨inferInstance, ?_⟩)
      intro x
      obtain ⟨k, hk⟩ := hB2 (x : ↥B)
      exact ⟨k, Subtype.ext hk⟩
    rw [htop']
    exact Subgroup.index_top
  ·
    set φ : ↥B →* alternatingGroup (Fin m) := α.comp (Subgroup.inclusion hBK) with hφ
    have hφs : Function.Surjective φ := by
      intro a
      have : a ∈ (B.subgroupOf K).map α := by rw [htop]; trivial
      obtain ⟨k, hk, hka⟩ := this
      exact ⟨⟨(k : G), Subgroup.mem_subgroupOf.1 hk⟩, by show α _ = a; exact hka⟩
    have hkerle : φ.ker ≤ CFSG.pCore 2 ↥B := by
      refine le_sSup ⟨φ.normal_ker, ?_⟩
      intro x
      refine ⟨1, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      have hx : α ⟨(x : ↥B), hBK (x : ↥B).2⟩ = 1 := x.2
      have := h.elem.2 _ (hmemE (x : ↥B) hx)
      simpa using this
    have hnorm : ((CFSG.pCore 2 ↥B).map φ).Normal := Subgroup.Normal.map CFSG.pCore_normal φ hφs
    rcases hs.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥B).map φ) with hb | ht
    · have hP : CFSG.pCore 2 ↥B = φ.ker := by
        refine le_antisymm ?_ hkerle
        intro x hx
        rw [MonoidHom.mem_ker]
        have : φ x ∈ (CFSG.pCore 2 ↥B).map φ := ⟨x, hx, rfl⟩
        rw [hb] at this
        exact this
      have hq : ↥B ⧸ CFSG.pCore 2 ↥B ≃* alternatingGroup (Fin m) :=
        (QuotientGroup.quotientMulEquivOfEq hP).trans
          (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
      right
      exact Nat.card_congr hq.toEquiv
    · left
      have hP : CFSG.pCore 2 ↥B = ⊤ := by
        refine eq_top_iff.2 fun b _ => ?_
        have : φ b ∈ (CFSG.pCore 2 ↥B).map φ := by rw [ht]; trivial
        obtain ⟨p, hp, hpb⟩ := this
        have : p⁻¹ * b ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hpb, inv_mul_cancel]
        have h2 := hkerle this
        have h3 := (CFSG.pCore 2 ↥B).mul_mem hp h2
        simpa using h3
      rw [hP]
      exact Subgroup.index_top

theorem quotOrder_ne (n : ℕ) (hn : 2 ≤ n) :
    2 ^ n * (4 ^ n - 1) ≠ 1 ∧ 2 ^ n * (4 ^ n - 1) ≠ 360 ∧ 2 ^ n * (4 ^ n - 1) ≠ 2520 := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> norm_num
  · have h1 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h2 : 4 ^ 4 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h3 : 16 * 255 ≤ 2 ^ n * (4 ^ n - 1) :=
      Nat.mul_le_mul (by simpa using h1) (by simp at h2; omega)
    omega

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem card_alt_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem Alt2Struct.not_hasChi0Block (h : Alt2Struct K E m)
    (hs : IsSimpleGroup (alternatingGroup (Fin m)))
    (hm : Nat.card (alternatingGroup (Fin m)) = 360 ∨ Nat.card (alternatingGroup (Fin m)) = 2520) :
    ¬ HasChi0Block K := by
  rintro ⟨B, ⟨⟨hsh, hBK, hsub⟩, htype⟩⟩
  have hdich := h.quotient_card hs hBK hsub
  have hord := card_quotient_of_chi0Type htype
  rcases hdich with h1 | h1
  · rcases hord with h3 | h3 | ⟨n, hn, h3⟩
    · omega
    · omega
    · exact (quotOrder_ne n hn).1 (h3.symm.trans h1)
  · rcases hord with h3 | h3 | ⟨n, hn, h3⟩
    · rcases hm with hm | hm <;> omega
    · rcases hm with hm | hm <;> omega
    · rcases hm with hm | hm
      · exact (quotOrder_ne n hn).2.1 (h3.symm.trans (h1.trans hm))
      · exact (quotOrder_ne n hn).2.2 (h3.symm.trans (h1.trans hm))

end Block

section Map

variable {X G : Type*} [Group X] [Group G] {K E : Subgroup X} {m : ℕ}

theorem Alt2Struct.map (h : Alt2Struct K E m) (f : X →* G) (hf : Function.Injective f) :
    Alt2Struct (K.map f) (E.map f) m where
  le := Subgroup.map_mono h.le
  elem := by
    obtain ⟨hc, hp⟩ := h.elem
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      show (a : G) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hc.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hp x hx, map_one]
  card := by
    rw [Subgroup.card_map_of_injective hf]
    exact h.card
  hom := by
    obtain ⟨α, hα, hker⟩ := h.hom
    let e : ↥K ≃* ↥(K.map f) := Subgroup.equivMapOfInjective K f hf
    refine ⟨α.comp e.symm.toMonoidHom, hα.comp e.symm.surjective, ?_⟩
    ext x
    have hx : ((e.symm x : ↥K) : X) ∈ E ↔ (x : G) ∈ E.map f := by
      have h1 : (x : G) = f ((e.symm x : ↥K) : X) := by
        have := Subgroup.coe_equivMapOfInjective_apply K f hf (e.symm x)
        simpa [e] using this
      rw [h1]
      exact (Subgroup.mem_map_iff_mem hf).symm
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hx]
    show α (e.symm x) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  noncentral := by
    obtain ⟨k, hk, e, he, hne⟩ := h.noncentral
    refine ⟨f k, Subgroup.mem_map_of_mem f hk, f e, Subgroup.mem_map_of_mem f he, fun hc => hne ?_⟩
    apply hf
    rw [map_mul, map_mul]
    exact hc

end Map

end CFSG.QuasithinUnique.Vol2Native.L239
