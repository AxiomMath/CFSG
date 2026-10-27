module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSkeleton
public import CFSG.GroupTheory.PGroup.RankTwoCommute
public import CFSG.GroupTheory.PCore.RelPPrimeCoreMap

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

section Rank

variable {G : Type*} [Group G] [Finite G]

theorem two_le_pRank_of_commuting_subgroups {f : ℕ} [hf : Fact f.Prime] {K X₁ X₂ : Subgroup G}
    (h₁ : X₁ ≤ K) (h₂ : X₂ ≤ K) (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, Commute a b)
    (hdisj : X₁ ⊓ X₂ = ⊥) (hf₁ : f ∣ Nat.card X₁) (hf₂ : f ∣ Nat.card X₂) :
    2 ≤ CFSG.Open.pRank f K := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X₁) f hf₁
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥X₂) f hf₂
  have hx' : orderOf (x : G) = f := by rw [Subgroup.orderOf_coe]; exact hx
  have hy' : orderOf (y : G) = f := by rw [Subgroup.orderOf_coe]; exact hy
  refine CFSG.GroupTheory.two_le_pRank_of_commute (h₁ x.2) (h₂ y.2) hx' hy'
    (hcomm _ x.2 _ y.2) fun hyx => ?_
  have hyX₁ : (y : G) ∈ X₁ := (zpowers_le.mpr x.2) hyx
  have : (y : G) ∈ X₁ ⊓ X₂ := mem_inf.mpr ⟨hyX₁, y.2⟩
  rw [hdisj, mem_bot] at this
  rw [this, orderOf_one] at hy'
  exact hf.out.one_lt.ne hy'

end Rank

section Basic

theorem normal_of_conj' {A : Type*} [Group A] {N X : Subgroup A}
    (h : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) : (N.subgroupOf X).Normal :=
  ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    simpa using h g g.2 n hn⟩

theorem conj_mem_of_normal' {A : Type*} [Group A] {N X : Subgroup A}
    (h : (N.subgroupOf X).Normal) {x n : A} (hx : x ∈ X) (hn : n ∈ N) (hnX : n ∈ X) :
    x * n * x⁻¹ ∈ N := by
  have := h.conj_mem ⟨n, hnX⟩ (mem_subgroupOf.mpr hn) ⟨x, hx⟩
  simpa [mem_subgroupOf] using this

theorem _root_.CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622IsSimpleSection.map_of_injective
    {B A : Type} [Group B] [Group A] (f : B →* A) (hf : Function.Injective f)
    {L D : Subgroup B} (h : S622IsSimpleSection L D) :
    S622IsSimpleSection (L.map f) (D.map f) := by
  obtain ⟨hDL, hn, hne, hsimp, hnab⟩ := h
  refine ⟨Subgroup.map_mono hDL, ?_, ?_, ?_, ?_⟩
  · refine normal_of_conj' fun x hx n hn' => ?_
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨n', hn'', rfl⟩ := hn'
    exact ⟨x' * n' * x'⁻¹, conj_mem_of_normal' hn hx' hn'' (hDL hn''), by simp⟩
  · exact fun heq => hne (Subgroup.map_injective hf heq)
  · intro N hDN hNL hNn
    have hNr : N ≤ f.range := hNL.trans (Subgroup.map_le_range f L)
    have hNN' : (N.comap f).map f = N := Subgroup.map_comap_eq_self hNr
    have hDN' : D ≤ N.comap f := fun d hd => hDN ⟨d, hd, rfl⟩
    have hNL' : N.comap f ≤ L := by
      intro x hx
      obtain ⟨l, hl, hlx⟩ := hNL (show f x ∈ N from hx)
      exact (hf hlx) ▸ hl
    have hNn' : ((N.comap f).subgroupOf L).Normal := by
      refine normal_of_conj' fun x hx n hn' => ?_
      have h1 : f x ∈ L.map f := ⟨x, hx, rfl⟩
      have h2 : f n ∈ N := hn'
      have h3 : f n ∈ L.map f := ⟨n, hNL' hn', rfl⟩
      have h4 : f x * f n * (f x)⁻¹ ∈ N := conj_mem_of_normal' hNn h1 h2 h3
      change f (x * n * x⁻¹) ∈ N
      simpa using h4
    rcases hsimp _ hDN' hNL' hNn' with h1 | h1
    · left
      rw [← hNN', h1]
    · right
      rw [← hNN', h1]
  · intro hall
    apply hnab
    intro a ha b hb
    have := hall (f a) ⟨a, ha, rfl⟩ (f b) ⟨b, hb, rfl⟩
    obtain ⟨d, hd, hde⟩ := this
    have : d = a * b * a⁻¹ * b⁻¹ := hf (by simpa using hde)
    exact this ▸ hd

theorem _root_.CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622IsSimpleSection.of_surjective
    {A : Type} [Group A] {Y : Subgroup A} {T : Type} [Group T] [IsSimpleGroup T]
    (φ : ↥Y →* T) (hφ : Function.Surjective φ) (hnab : ∃ a b : T, a * b ≠ b * a) :
    S622IsSimpleSection Y (φ.ker.map Y.subtype) := by
  have hsub : (φ.ker.map Y.subtype).subgroupOf Y = φ.ker :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective φ.ker
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · rw [hsub]
    exact MonoidHom.normal_ker φ
  · intro h
    have htop : φ.ker = ⊤ := by
      have h2 : (φ.ker.map Y.subtype).subgroupOf Y = Y.subgroupOf Y := by rw [h]
      rwa [hsub, Subgroup.subgroupOf_self] at h2
    obtain ⟨a, b, hab⟩ := hnab
    obtain ⟨x, rfl⟩ := hφ a
    obtain ⟨y, rfl⟩ := hφ b
    apply hab
    rw [MonoidHom.mem_ker.mp (htop ▸ mem_top x), MonoidHom.mem_ker.mp (htop ▸ mem_top y)]
  · intro N hDN hNY hNn
    have hker : φ.ker ≤ N.subgroupOf Y := by
      intro x hx
      exact hDN ⟨x, hx, rfl⟩
    have hNm : (N.subgroupOf Y).map Y.subtype = N := Subgroup.map_subgroupOf_eq_of_le hNY
    haveI : (N.subgroupOf Y).Normal := hNn
    haveI : ((N.subgroupOf Y).map φ).Normal := Subgroup.Normal.map ‹_› φ hφ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf Y).map φ) with h | h
    · left
      have : N.subgroupOf Y ≤ φ.ker := (Subgroup.map_eq_bot_iff _).mp h
      rw [← hNm, le_antisymm this hker]
    · right
      have htop : N.subgroupOf Y = ⊤ := by
        rw [eq_top_iff]
        intro y _
        have hy : φ y ∈ (N.subgroupOf Y).map φ := h ▸ mem_top _
        obtain ⟨n, hn, hny⟩ := hy
        have : y * n⁻¹ ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hny, mul_inv_cancel]
        have h3 := hker this
        simpa using mul_mem h3 hn
      rw [← hNm, htop, Subgroup.map_top, Subgroup.range_subtype]
  · intro hall
    obtain ⟨a, b, hab⟩ := hnab
    obtain ⟨x, rfl⟩ := hφ a
    obtain ⟨y, rfl⟩ := hφ b
    apply hab
    obtain ⟨k, hk, hke⟩ := hall (x : A) x.2 (y : A) y.2
    have hk' : k = x * y * x⁻¹ * y⁻¹ := Subtype.ext (by simpa using hke)
    have h1 : φ (x * y * x⁻¹ * y⁻¹) = 1 := hk' ▸ MonoidHom.mem_ker.mp hk
    simp only [map_mul, map_inv] at h1
    calc φ x * φ y = (φ x * φ y * (φ x)⁻¹ * (φ y)⁻¹) * (φ y * φ x) := by group
      _ = φ y * φ x := by rw [h1, one_mul]

end Basic

@[expose] def LeviSubAt (S : Type) [Group S] [Finite S] : Prop :=
  ∀ (K₀ : Subgroup S) (p : ℕ), ¬ fusionIsBenderGroup S → p.Prime → 5 ≤ p →
    CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1 → IsParabolicTwo S ⊤ K₀ → K₀ ≠ ⊤ →
    (∀ U : Subgroup S, CFSG.ABGLocalTools.IsSylowOf 2 U K₀ →
      ¬ U ≤ rankThreePrimeCore p K₀) →
    ∃ (f : ℕ) (Y W : Subgroup S), f.Prime ∧ f ≠ 2 ∧ f ≠ p ∧
      2 ≤ CFSG.Open.pRank f (⊤ : Subgroup S) ∧
      Y ≤ K₀ ∧ S622IsSimpleSection Y W ∧ f ∣ W.relIndex Y ∧
      p ∣ W.relIndex Y ∧ ¬ p ∣ Nat.card W

theorem dvd_card_of_sylow_hyp {S : Type} [Group S] [Finite S] {K₀ : Subgroup S} {p : ℕ}
    (hp : p.Prime)
    (hsyl : ∀ U : Subgroup S, CFSG.ABGLocalTools.IsSylowOf 2 U K₀ →
      ¬ U ≤ rankThreePrimeCore p K₀) : p ∣ Nat.card K₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hdvd
  obtain ⟨U, hU⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 K₀
  refine hsyl U hU (hU.le.trans (le_sSup ⟨le_rfl, ?_, ?_⟩))
  · rw [Subgroup.subgroupOf_self]
    infer_instance
  · exact (Nat.Prime.coprime_iff_not_dvd hp).2 hdvd

theorem kFactParabolicLeviSub_of_leviSubAt
    (h : ∀ (S : Type) [Group S] [Finite S], IsChevSimple 2 S → LeviSubAt S) :
    KFactParabolicLeviSub := by
  intro A _ _ K K₀ p hK hB hp h5 hrank hpar hne hsyl
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hat := h ↥K hK
  obtain ⟨hK₀K, U, hU, hUN⟩ := hpar
  have hUK : U ≤ K := hU.le
  have hmapK₀ : (K₀.subgroupOf K).map K.subtype = K₀ := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK₀K]
  have hpar' : IsParabolicTwo ↥K ⊤ (K₀.subgroupOf K) := by
    refine ⟨le_top, U.subgroupOf K, ?_, ?_⟩
    · obtain ⟨Q, hQ⟩ := hU.exists_sylow_eq_subgroupOf
      rw [← hQ]
      exact (CFSG.ABGLocalTools.isSylowOf_iff).2 ⟨le_top, Q.isPGroup', by
        rw [Subgroup.relIndex_top_right]; exact Q.not_dvd_index⟩
    · rintro g ⟨hgN, -⟩
      have h1 : (g : A) ∈ normalizer (U : Set A) := by
        have := hgN
        rw [← Subgroup.subgroupOf_normalizer_eq hUK] at this
        exact this
      exact Subgroup.mem_subgroupOf.mpr (hUN ⟨h1, g.2⟩)
  have hsyl' : ∀ U' : Subgroup ↥K, CFSG.ABGLocalTools.IsSylowOf 2 U' (K₀.subgroupOf K) →
      ¬ U' ≤ rankThreePrimeCore p (K₀.subgroupOf K) := by
    intro U' hU' hcore
    refine hsyl (U'.map K.subtype) ?_ ?_
    · rw [CFSG.ABGLocalTools.isSylowOf_iff] at hU' ⊢
      obtain ⟨hle, hp2, hdvd⟩ := hU'
      refine ⟨Subgroup.map_le_iff_le_comap.mpr hle, hp2.map K.subtype, ?_⟩
      have := Subgroup.relIndex_map_map_of_injective U' (K₀.subgroupOf K) K.subtype_injective
      intro hd
      apply hdvd
      rw [← this, hmapK₀]
      exact hd
    · calc U'.map K.subtype ≤ (rankThreePrimeCore p (K₀.subgroupOf K)).map K.subtype :=
            Subgroup.map_mono hcore
        _ ≤ rankThreePrimeCore p ((K₀.subgroupOf K).map K.subtype) :=
            relPPrimeCore_map_le_of_injective K.subtype K.subtype_injective _ p
        _ = rankThreePrimeCore p K₀ := by rw [hmapK₀]
  have hne' : K₀.subgroupOf K ≠ ⊤ := fun htop =>
    hne (le_antisymm hK₀K (Subgroup.subgroupOf_eq_top.mp htop))
  have hrank' : CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 1 := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
  obtain ⟨f, Y', W', hf, hf2, hfp, hfr, hYK₀, hYW, hfYW, hpYW, hpW⟩ :=
    hat (K₀.subgroupOf K) p hB hp h5 hrank' hpar' hne' hsyl'
  refine ⟨f, Y'.map K.subtype, W'.map K.subtype, hf, hf2, hfp, ?_, ?_,
    hYW.map_of_injective K.subtype K.subtype_injective, ?_, ?_, ?_⟩
  · rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
  · exact Subgroup.map_le_iff_le_comap.mpr hYK₀
  · rwa [Subgroup.relIndex_map_map_of_injective _ _ K.subtype_injective]
  · rwa [Subgroup.relIndex_map_map_of_injective _ _ K.subtype_injective]
  · rwa [Subgroup.card_map_of_injective K.subtype_injective]

section Equiv

variable {S S' : Type} [Group S] [Finite S] [Group S'] [Finite S']

theorem bender_of_mulEquiv (e : S ≃* S') (h : fusionIsBenderGroup S') : fusionIsBenderGroup S := by
  rcases h with ⟨f, hf, ⟨m⟩⟩ | ⟨f, hf, ⟨m⟩⟩ | ⟨a, ha, ⟨m⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.trans m⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.trans m⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.trans m⟩⟩)

theorem map_symm_map (e : S ≃* S') (X : Subgroup S) :
    (X.map e.toMonoidHom).map e.symm.toMonoidHom = X := by
  rw [Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id S := by ext x; simp
  rw [this, Subgroup.map_id]

theorem isSylowOf_map (e : S ≃* S') {p : ℕ} [Fact p.Prime] {U K : Subgroup S}
    (h : CFSG.ABGLocalTools.IsSylowOf p U K) :
    CFSG.ABGLocalTools.IsSylowOf p (U.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  obtain ⟨hle, hp, hdvd⟩ := h
  refine ⟨Subgroup.map_mono hle, hp.map e.toMonoidHom, ?_⟩
  rwa [Subgroup.relIndex_map_map_of_injective _ _ e.injective]

theorem symm_mem_normalizer_map (e : S ≃* S') {U : Subgroup S} {g : S'}
    (hg : g ∈ normalizer ((U.map e.toMonoidHom : Subgroup S') : Set S')) :
    e.symm g ∈ normalizer (U : Set S) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  have h1 := hg (e x)
  have hx : e x ∈ U.map e.toMonoidHom ↔ x ∈ U :=
    Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective
  have hy : g * e x * g⁻¹ = e (e.symm g * x * (e.symm g)⁻¹) := by simp
  have hz : g * e x * g⁻¹ ∈ U.map e.toMonoidHom ↔ e.symm g * x * (e.symm g)⁻¹ ∈ U := by
    rw [hy]
    exact Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective
  rw [← hx, h1, hz]

@[expose] def LeviAt {S : Type} [Group S] [Finite S] (K₀ : Subgroup S) (p : ℕ) : Prop :=
  ¬ fusionIsBenderGroup S → p.Prime → 5 ≤ p →
    CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1 → IsParabolicTwo S ⊤ K₀ → K₀ ≠ ⊤ →
    (∀ U : Subgroup S, CFSG.ABGLocalTools.IsSylowOf 2 U K₀ →
      ¬ U ≤ rankThreePrimeCore p K₀) →
    ∃ (f : ℕ) (Y W : Subgroup S), f.Prime ∧ f ≠ 2 ∧ f ≠ p ∧
      2 ≤ CFSG.Open.pRank f (⊤ : Subgroup S) ∧
      Y ≤ K₀ ∧ S622IsSimpleSection Y W ∧ f ∣ W.relIndex Y ∧
      p ∣ W.relIndex Y ∧ ¬ p ∣ Nat.card W

theorem LeviAt.of_map (e : S ≃* S') {K₀ : Subgroup S} {p : ℕ}
    (h : LeviAt (K₀.map e.toMonoidHom) p) : LeviAt K₀ p := by
  intro hB hp h5 hrank hpar hne hsyl
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hK₀, U, hU, hUN⟩ := hpar
  have hpar' : IsParabolicTwo S' ⊤ (K₀.map e.toMonoidHom) := by
    refine ⟨le_top, U.map e.toMonoidHom, ?_, ?_⟩
    · have := isSylowOf_map e hU
      rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
    · rintro g ⟨hg, -⟩
      have h1 := hUN ⟨symm_mem_normalizer_map e hg, mem_top _⟩
      have : g = e (e.symm g) := by simp
      rw [this]
      exact ⟨_, h1, rfl⟩
  have hne' : K₀.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hne
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rwa [map_symm_map, Subgroup.map_top_of_surjective _ e.symm.surjective] at this
  have hrank' : CFSG.Open.pRank p (⊤ : Subgroup S') ≤ 1 := by
    rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  have hsyl' : ∀ U' : Subgroup S', CFSG.ABGLocalTools.IsSylowOf 2 U' (K₀.map e.toMonoidHom) →
      ¬ U' ≤ rankThreePrimeCore p (K₀.map e.toMonoidHom) := by
    intro U' hU' hcore
    refine hsyl (U'.map e.symm.toMonoidHom) ?_ ?_
    · have := isSylowOf_map e.symm hU'
      rwa [show (K₀.map e.toMonoidHom).map e.symm.toMonoidHom = K₀ from map_symm_map e K₀] at this
    · calc U'.map e.symm.toMonoidHom
          ≤ (rankThreePrimeCore p (K₀.map e.toMonoidHom)).map e.symm.toMonoidHom :=
            Subgroup.map_mono hcore
        _ = rankThreePrimeCore p ((K₀.map e.toMonoidHom).map e.symm.toMonoidHom) :=
            (relPPrimeCore_map_mulEquiv e.symm _ p).symm
        _ = rankThreePrimeCore p K₀ := by rw [map_symm_map]
  have hB' : ¬ fusionIsBenderGroup S' := fun hb => hB (bender_of_mulEquiv e hb)
  obtain ⟨f, Y', W', hf, hf2, hfp, hfr, hYK₀, hYW, hfYW, hpYW, hpW⟩ :=
    h hB' hp h5 hrank' hpar' hne' hsyl'
  refine ⟨f, Y'.map e.symm.toMonoidHom, W'.map e.symm.toMonoidHom, hf, hf2, hfp, ?_, ?_,
    hYW.map_of_injective e.symm.toMonoidHom e.symm.injective, ?_, ?_, ?_⟩
  · rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hf.one_lt e] at hfr
  · calc Y'.map e.symm.toMonoidHom ≤ (K₀.map e.toMonoidHom).map e.symm.toMonoidHom :=
          Subgroup.map_mono hYK₀
      _ = K₀ := map_symm_map e K₀
  · rwa [Subgroup.relIndex_map_map_of_injective _ _ e.symm.injective]
  · rwa [Subgroup.relIndex_map_map_of_injective _ _ e.symm.injective]
  · rwa [Subgroup.card_map_of_injective e.symm.injective]

theorem LeviSubAt.of_mulEquiv (e : S ≃* S') (h : LeviSubAt S') : LeviSubAt S :=
  fun K₀ p => LeviAt.of_map e (h _ p)

theorem LeviAt.of_conj (g : S) {K₀ : Subgroup S} {p : ℕ}
    (h : LeviAt (K₀.map (MulAut.conj g).toMonoidHom) p) : LeviAt K₀ p :=
  LeviAt.of_map (MulAut.conj g) h

theorem normalizer_map_conj' (x : S) (H : Subgroup S) :
    normalizer ((H.map (MulAut.conj x).toMonoidHom : Subgroup S) : Set S) =
      (normalizer (H : Set S)).map (MulAut.conj x).toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq H (MulAut.conj x)).symm

theorem leviSubAt_of_standard_sylow (T₀ : Sylow 2 S)
    (h : ∀ (K₀ : Subgroup S) (p : ℕ), normalizer ((T₀ : Subgroup S) : Set S) ≤ K₀ →
      LeviAt K₀ p) : LeviSubAt S := by
  intro K₀ p
  by_cases hpar : IsParabolicTwo S ⊤ K₀
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨hK₀, U, hU, hUN⟩ := hpar
    obtain ⟨-, hU2, hUdvd⟩ := (CFSG.ABGLocalTools.isSylowOf_iff).1 hU
    rw [Subgroup.relIndex_top_right] at hUdvd
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S T₀ (hU2.toSylow hUdvd)
    have hUg : U = (T₀ : Subgroup S).map (MulAut.conj g).toMonoidHom := by
      have h1 : ((g • T₀ : Sylow 2 S) : Subgroup S) = U := by
        rw [hg, IsPGroup.toSylow_coe]
      rw [← h1, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    have hN : normalizer ((T₀ : Subgroup S) : Set S) ≤
        K₀.map (MulAut.conj g⁻¹).toMonoidHom := by
      intro x hx
      have hx' : g * x * g⁻¹ ∈ normalizer (U : Set S) := by
        rw [hUg, normalizer_map_conj']
        exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
      refine ⟨g * x * g⁻¹, hUN ⟨hx', mem_top _⟩, ?_⟩
      show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
      group
    exact LeviAt.of_conj g⁻¹ (h _ p hN)
  · intro _ _ _ _ hpar'
    exact absurd hpar' hpar

end Equiv

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
