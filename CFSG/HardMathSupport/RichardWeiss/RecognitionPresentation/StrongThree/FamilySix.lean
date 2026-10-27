module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.AltSix
public import CFSG.Quasithin.Vol2.KGFact12617LieW
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Families
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open

theorem alt6_card_dvd {X : Type} [Group X] [Finite X] (K : Subgroup X) (hKn : K.Normal)
    (e : K ≃* alternatingGroup (Fin 6)) (hKc : Subgroup.centralizer (K : Set X) = ⊥) :
    Nat.card X ∣ 1440 := by
  have hinj : Function.Injective (Subgroup.normalizerMonoidHom K) := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have hmem : n ∈ (Subgroup.normalizerMonoidHom K).ker := hn
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, hKc, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hdvd : Nat.card (Subgroup.normalizer (K : Set X)) ∣ Nat.card (MulAut ↥K) :=
    Subgroup.card_dvd_of_injective (Subgroup.normalizerMonoidHom K) hinj
  have hcard : Nat.card (MulAut ↥K) = Nat.card (MulAut ↥(alternatingGroup (Fin 6))) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have hnorm : Nat.card (Subgroup.normalizer (K : Set X)) = Nat.card X := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hKn, Subgroup.card_top]
  obtain ⟨h720, hle⟩ := CFSG.Quasithin.H13.KG12617Lie.card_mulAut_alt6
  have haut : Nat.card (MulAut ↥(alternatingGroup (Fin 6))) ∣ 1440 := by
    obtain ⟨m, hm⟩ := h720
    have hpos : 0 < Nat.card (MulAut ↥(alternatingGroup (Fin 6))) := Nat.card_pos
    have hm12 : m = 1 ∨ m = 2 := by omega
    rcases hm12 with rfl | rfl
    · exact ⟨2, by omega⟩
    · exact ⟨1, by omega⟩
  rw [← hnorm]
  exact hdvd.trans (by rw [hcard]; exact haut)

theorem alt6_card_K {X : Type} [Group X] (K : Subgroup X)
    (e : K ≃* alternatingGroup (Fin 6)) : Nat.card K = 360 := by
  rw [Nat.card_congr e.toEquiv, alt6_A6_card]

theorem alt6_index_K_dvd {X : Type} [Group X] [Finite X] (K : Subgroup X)
    (e : K ≃* alternatingGroup (Fin 6)) (hX : Nat.card X ∣ 1440) : K.index ∣ 4 := by
  have h1 : Nat.card K * K.index = Nat.card X := Subgroup.card_mul_index K
  rw [alt6_card_K K e] at h1
  refine (Nat.mul_dvd_mul_iff_left (show 0 < 360 by norm_num)).1 ?_
  rw [show 360 * 4 = 1440 by norm_num, h1]
  exact hX

theorem alt6_sylow_card {X : Type} [Group X] [Finite X] (K : Subgroup X)
    (e : K ≃* alternatingGroup (Fin 6)) (hX : Nat.card X ∣ 1440) (P : Sylow 3 X) :
    Nat.card (P : Subgroup X) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKX : 360 ∣ Nat.card X := by
    rw [← alt6_card_K K e]
    exact Subgroup.card_subgroup_dvd_card K
  have hPX : Nat.card (P : Subgroup X) * (P : Subgroup X).index = Nat.card X :=
    Subgroup.card_mul_index (P : Subgroup X)
  have hnd : ¬ 3 ∣ (P : Subgroup X).index := Sylow.not_dvd_index P
  have hcop : Nat.Coprime 9 (P : Subgroup X).index := by
    have h3 : Nat.Coprime 3 (P : Subgroup X).index :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd
    exact Nat.Coprime.pow_left 2 h3
  have h9X : 9 ∣ Nat.card (P : Subgroup X) * (P : Subgroup X).index := by
    rw [hPX]
    exact (show 9 ∣ 360 by norm_num).trans hKX
  have h9P : 9 ∣ Nat.card (P : Subgroup X) := hcop.dvd_of_dvd_mul_right h9X
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 P.isPGroup'
  have hdvdP : Nat.card (P : Subgroup X) ∣ 1440 :=
    (Subgroup.card_subgroup_dvd_card (P : Subgroup X)).trans hX
  rw [hn] at h9P hdvdP ⊢
  have hn3 : n < 3 := by
    by_contra hcon
    have h27 : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
    have := h27.trans hdvdP
    norm_num at this
  interval_cases n
  all_goals first
    | rfl
    | (exfalso; norm_num at h9P)

theorem alt6_sylow_le {X : Type} [Group X] [Finite X] (K : Subgroup X) (hKn : K.Normal)
    (e : K ≃* alternatingGroup (Fin 6)) (hX : Nat.card X ∣ 1440) (P : Sylow 3 X) :
    (P : Subgroup X) ≤ K ∧ Nat.card (P : Subgroup X) = 9 := by
  have hc := alt6_sylow_card K e hX P
  refine ⟨?_, hc⟩
  have := hKn
  let f : (P : Subgroup X) →* X ⧸ K := (QuotientGroup.mk' K).comp (P : Subgroup X).subtype
  have h9 : Nat.card f.range ∣ 9 := by
    rw [← hc]
    exact Subgroup.card_dvd_of_surjective (f := f.rangeRestrict)
      (MonoidHom.rangeRestrict_surjective f)
  have h4 : Nat.card f.range ∣ 4 :=
    (Subgroup.card_subgroup_dvd_card f.range).trans (alt6_index_K_dvd K e hX)
  have hone : Nat.card f.range = 1 :=
    Nat.dvd_one.1 (by have := Nat.dvd_gcd h9 h4; simpa using this)
  have hbot : f.range = ⊥ := Subgroup.eq_bot_of_card_eq f.range hone
  intro x hx
  have hmem : f ⟨x, hx⟩ ∈ f.range := ⟨⟨x, hx⟩, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have h1 : ((x : X) : X ⧸ K) = 1 := hmem
  exact (QuotientGroup.eq_one_iff x).1 h1

@[expose] def alt6_sylowOf {G : Type} [Group G] [Finite G] (S : Subgroup G)
    (hS : Nat.card S = 9) (hG : ¬ 27 ∣ Nat.card G) : Sylow 3 G where
  toSubgroup := S
  isPGroup' := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPGroup.iff_card.2 ⟨2, by rw [hS]; norm_num⟩
  is_maximal' := by
    intro Q hQ hSQ
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
    have h9 : 9 ∣ Nat.card Q := by
      rw [← hS]
      exact Subgroup.card_dvd_of_le hSQ
    rw [hn] at h9
    have hn2 : n ≤ 2 := by
      by_contra hcon
      apply hG
      have h27 : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
      have h27Q : 27 ∣ Nat.card Q := by
        rw [hn]
        exact h27
      exact h27Q.trans (Subgroup.card_subgroup_dvd_card Q)
    have hQc : Nat.card Q = 9 := by
      rw [hn]
      interval_cases n
      all_goals first
        | rfl
        | (exfalso; norm_num at h9)
    exact (Subgroup.eq_of_le_of_card_ge hSQ (by rw [hQc, hS])).symm

theorem alt6_exists_iso {X : Type} [Group X] [Finite X] (K P : Subgroup X)
    (e : K ≃* alternatingGroup (Fin 6)) (hP9 : Nat.card (P ⊓ K : Subgroup X) = 9) :
    ∃ φ : K ≃* alternatingGroup (Fin 6),
      (Subgroup.map φ.toMonoidHom ((P ⊓ K).subgroupOf K)).map (alternatingGroup (Fin 6)).subtype
        = alt6_Q0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdiv : ¬ 27 ∣ Nat.card (alternatingGroup (Fin 6)) := by
    rw [alt6_A6_card]
    norm_num
  set S₁ : Subgroup (alternatingGroup (Fin 6)) :=
    Subgroup.map e.toMonoidHom ((P ⊓ K).subgroupOf K) with hS₁def
  have hS₁card : Nat.card S₁ = 9 := by
    rw [hS₁def, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : P ⊓ K ≤ K)).toEquiv, hP9]
  have hQ0card : Nat.card (alt6_Q0.subgroupOf (alternatingGroup (Fin 6))) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe alt6_Q0_le).toEquiv, alt6_Q0_card]
  let P₁ := alt6_sylowOf S₁ hS₁card hdiv
  let P₂ := alt6_sylowOf (alt6_Q0.subgroupOf (alternatingGroup (Fin 6))) hQ0card hdiv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) P₁ P₂
  have hconj : Subgroup.map (MulAut.conj g).toMonoidHom S₁ =
      alt6_Q0.subgroupOf (alternatingGroup (Fin 6)) := by
    have h := congrArg Sylow.toSubgroup hg
    rw [Sylow.smul_def] at h
    exact h
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have hφ : (e.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := rfl
  rw [hφ, ← Subgroup.map_map, ← hS₁def, hconj, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left alt6_Q0_le]

theorem pRank_three_bot {X : Type} [Group X] [Finite X] :
    CFSG.Open.pRank 3 (⊥ : Subgroup X) = 0 := by
  unfold CFSG.Open.pRank
  apply le_antisymm
  · apply csSup_le'
    rintro k ⟨E, hE, -, hcard⟩
    have hEb : E = ⊥ := le_bot_iff.1 hE
    subst hEb
    rw [Subgroup.card_bot] at hcard
    rcases Nat.eq_zero_or_pos k with h | h
    · omega
    · exfalso
      have h3 : 3 ≤ 3 ^ k := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega
  · exact Nat.zero_le _

theorem ne_bot_of_one_le_pRank_three {X : Type} [Group X] [Finite X] {R : Subgroup X}
    (h : 1 ≤ CFSG.Open.pRank 3 R) : R ≠ ⊥ := by
  rintro rfl
  rw [pRank_three_bot] at h
  omega

theorem le_pRank_three_of_elemAbelian {X : Type} [Group X] [Finite X] {R : Subgroup X}
    (hE : IsElemAbelian 3 R) (k : ℕ) (hk : Nat.card R = 3 ^ k) :
    k ≤ CFSG.Open.pRank 3 R := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hE hk

theorem alt6_isElemAbelian_of_iso {X : Type} [Group X] [Finite X] (K P : Subgroup X)
    (φ : K ≃* alternatingGroup (Fin 6))
    (hQ : (Subgroup.map φ.toMonoidHom ((P ⊓ K).subgroupOf K)).map (alternatingGroup (Fin 6)).subtype
      = alt6_Q0) :
    IsElemAbelian 3 (P ⊓ K) := by
  have key : ∀ x : X, ∀ hx : x ∈ P ⊓ K,
      ((φ ⟨x, (Subgroup.mem_inf.1 hx).2⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))
        ∈ alt6_Q0 := by
    intro x hx
    have h1 : φ ⟨x, (Subgroup.mem_inf.1 hx).2⟩ ∈
        Subgroup.map φ.toMonoidHom ((P ⊓ K).subgroupOf K) :=
      Subgroup.mem_map.2 ⟨⟨x, (Subgroup.mem_inf.1 hx).2⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    have h2 : ((φ ⟨x, (Subgroup.mem_inf.1 hx).2⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) ∈
        (Subgroup.map φ.toMonoidHom ((P ⊓ K).subgroupOf K)).map (alternatingGroup (Fin 6)).subtype :=
      Subgroup.mem_map.2 ⟨φ ⟨x, (Subgroup.mem_inf.1 hx).2⟩, h1, rfl⟩
    rw [hQ] at h2
    exact h2
  unfold IsElemAbelian
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · have ha := key a.1 a.2
    have hb := key b.1 b.2
    have hcomm := alt6_elems9_comm _ ((alt6_mem_Q0_iff _).1 ha) _ ((alt6_mem_Q0_iff _).1 hb)
    have hφ : φ (⟨a.1, (Subgroup.mem_inf.1 a.2).2⟩ * ⟨b.1, (Subgroup.mem_inf.1 b.2).2⟩) =
        φ (⟨b.1, (Subgroup.mem_inf.1 b.2).2⟩ * ⟨a.1, (Subgroup.mem_inf.1 a.2).2⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext hcomm
    have hK := congrArg Subtype.val (φ.injective hφ)
    simpa using hK
  · intro x hx
    have hcube := alt6_elems9_cube _ ((alt6_mem_Q0_iff _).1 (key x hx))
    have hA : (φ ⟨x, (Subgroup.mem_inf.1 hx).2⟩) ^ 3 = 1 := Subtype.ext (by simpa using hcube)
    have hK : (⟨x, (Subgroup.mem_inf.1 hx).2⟩ : K) ^ 3 = 1 := by
      apply φ.injective
      rw [map_pow, hA, map_one]
    have := congrArg Subtype.val hK
    simpa using this

theorem alt6_normalizes_Q0_of_normalizes (a : Equiv.Perm (Fin 6))
    (ha : a ∈ alternatingGroup (Fin 6)) (R : Subgroup (Equiv.Perm (Fin 6)))
    (hR : R ≤ alt6_Q0) (hne : R ≠ ⊥)
    (haN : a ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin 6)))) :
    ∀ y : Equiv.Perm (Fin 6), y ∈ alt6_Q0 ↔ a * y * a⁻¹ ∈ alt6_Q0 := by
  have hS := alt6_normalizer_le_stab0 R hR hne a ha haN
  rw [alt6_stab0_eq] at hS
  have hN : alt6_Q0 ⊔ Subgroup.zpowers alt6_j ≤
      Subgroup.normalizer (alt6_Q0 : Set (Equiv.Perm (Fin 6))) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 alt6_jPerm_mem.2)
  intro y
  exact Subgroup.mem_normalizer_iff.1 (hN hS) y

theorem alt6_normalizer_transfer {X : Type} [Group X] [Finite X] (K P : Subgroup X)
    (hKn : K.Normal) (φ : K ≃* alternatingGroup (Fin 6))
    (hQ : (Subgroup.map φ.toMonoidHom ((P ⊓ K).subgroupOf K)).map (alternatingGroup (Fin 6)).subtype
      = alt6_Q0)
    (x : X) (hxK : x ∈ K) (R : Subgroup X) (hRQ : R ≤ P ⊓ K) (hR : R ≠ ⊥)
    (hxR : x ∈ Subgroup.normalizer (R : Set X)) :
    x ∈ Subgroup.normalizer ((P ⊓ K : Subgroup X) : Set X) := by
  set ψ : K →* Equiv.Perm (Fin 6) := (alternatingGroup (Fin 6)).subtype.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := fun a b h => φ.injective (Subtype.ext h)
  have hQψ : ((P ⊓ K).subgroupOf K).map ψ = alt6_Q0 := by
    rw [← hQ, Subgroup.map_map]
  have hmemQ : ∀ k : K, ψ k ∈ alt6_Q0 ↔ (k : X) ∈ P ⊓ K := by
    intro k
    rw [← hQψ]
    constructor
    · intro h
      obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.1 h
      have hsk : s = k := hψinj hse
      subst hsk
      exact Subgroup.mem_subgroupOf.1 hs
    · intro h
      exact Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.2 h)
  set Rp : Subgroup (Equiv.Perm (Fin 6)) := (R.subgroupOf K).map ψ with hRp
  have hRp_le : Rp ≤ alt6_Q0 := by
    rw [← hQψ]
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hy
    exact Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.2 (hRQ (Subgroup.mem_subgroupOf.1 hs)))
  have hRp_ne : Rp ≠ ⊥ := by
    obtain ⟨⟨r, hrR⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hR
    have hrK : r ∈ K := (Subgroup.mem_inf.1 (hRQ hrR)).2
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨ψ ⟨r, hrK⟩, Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.2 hrR)⟩, ?_⟩
    intro h
    apply hr1
    have h' : ψ ⟨r, hrK⟩ = 1 := congrArg Subtype.val h
    have h'' : (⟨r, hrK⟩ : K) = 1 := hψinj (h'.trans (map_one ψ).symm)
    have h3 : r = 1 := by simpa using congrArg Subtype.val h''
    exact Subtype.ext (by simpa using h3)
  have haN : ψ ⟨x, hxK⟩ ∈ Subgroup.normalizer (Rp : Set (Equiv.Perm (Fin 6))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hy
      have hconj : x * (s : X) * x⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.1 hxR (s : X)).1 (Subgroup.mem_subgroupOf.1 hs)
      have hcK : (⟨x, hxK⟩ : K) * s * (⟨x, hxK⟩ : K)⁻¹ ∈ R.subgroupOf K :=
        Subgroup.mem_subgroupOf.2 hconj
      have e : ψ ⟨x, hxK⟩ * ψ s * (ψ ⟨x, hxK⟩)⁻¹ =
          ψ (⟨x, hxK⟩ * s * (⟨x, hxK⟩ : K)⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      rw [e]
      exact Subgroup.mem_map_of_mem ψ hcK
    · intro hy
      obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.1 hy
      have hR' : x⁻¹ * (s : X) * x ∈ R := by
        apply (Subgroup.mem_normalizer_iff.1 hxR (x⁻¹ * (s : X) * x)).2
        have e : x * (x⁻¹ * (s : X) * x) * x⁻¹ = s := by group
        rw [e]
        exact Subgroup.mem_subgroupOf.1 hs
      have ht : (⟨x, hxK⟩ : K)⁻¹ * s * (⟨x, hxK⟩ : K) ∈ R.subgroupOf K :=
        Subgroup.mem_subgroupOf.2 hR'
      have hyt : y = ψ ((⟨x, hxK⟩ : K)⁻¹ * s * (⟨x, hxK⟩ : K)) := by
        rw [map_mul, map_mul, map_inv]
        rw [hse]
        group
      rw [hyt]
      exact Subgroup.mem_map_of_mem ψ ht
  have hNQ := alt6_normalizes_Q0_of_normalizes (ψ ⟨x, hxK⟩) (φ ⟨x, hxK⟩).2 Rp hRp_le hRp_ne haN
  rw [Subgroup.mem_normalizer_iff]
  intro h
  by_cases hhK : h ∈ K
  · have e1 : h ∈ P ⊓ K ↔ ψ ⟨h, hhK⟩ ∈ alt6_Q0 := (hmemQ ⟨h, hhK⟩).symm
    have e2 : x * h * x⁻¹ ∈ P ⊓ K ↔
        ψ (⟨x, hxK⟩ * ⟨h, hhK⟩ * (⟨x, hxK⟩ : K)⁻¹) ∈ alt6_Q0 :=
      (hmemQ (⟨x, hxK⟩ * ⟨h, hhK⟩ * (⟨x, hxK⟩ : K)⁻¹)).symm
    rw [e1, e2, map_mul, map_mul, map_inv]
    exact hNQ (ψ ⟨h, hhK⟩)
  · have hn1 : h ∉ P ⊓ K := fun hh => hhK (Subgroup.mem_inf.1 hh).2
    have hn2 : x * h * x⁻¹ ∉ P ⊓ K := by
      intro hh
      apply hhK
      have hK' : x * h * x⁻¹ ∈ K := (Subgroup.mem_inf.1 hh).2
      have hc := hKn.conj_mem _ hK' x⁻¹
      have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
      rw [e] at hc
      exact hc
    exact ⟨fun hh => absurd hh hn1, fun hh => absurd hh hn2⟩

theorem alt6_gammaCore_eq {X : Type} [Group X] [Finite X] (K P : Subgroup X) (hKn : K.Normal)
    (φ : K ≃* alternatingGroup (Fin 6))
    (hQ : (Subgroup.map φ.toMonoidHom ((P ⊓ K).subgroupOf K)).map (alternatingGroup (Fin 6)).subtype
      = alt6_Q0) :
    gammaCore 3 1 K (P ⊓ K) = K ⊓ Subgroup.normalizer ((P ⊓ K : Subgroup X) : Set X) := by
  have hP9 : Nat.card (P ⊓ K : Subgroup X) = 9 := by
    have h1 : Nat.card ((Subgroup.map φ.toMonoidHom ((P ⊓ K).subgroupOf K)).map
        (alternatingGroup (Fin 6)).subtype) = 9 := by
      rw [hQ, alt6_Q0_card]
    have hsub : Function.Injective (alternatingGroup (Fin 6)).subtype := Subtype.val_injective
    have hφinj : Function.Injective φ.toMonoidHom := φ.injective
    rw [Subgroup.card_map_of_injective hsub, Subgroup.card_map_of_injective hφinj] at h1
    have h2 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : P ⊓ K ≤ K)).toEquiv
    rw [← h2]
    exact h1
  unfold gammaCore
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨hxK, R, hRQ, hk, hxR⟩
    exact Subgroup.mem_inf.2
      ⟨hxK, alt6_normalizer_transfer K P hKn φ hQ x hxK R hRQ (ne_bot_of_one_le_pRank_three hk) hxR⟩
  · intro x hx
    apply Subgroup.subset_closure
    refine ⟨(Subgroup.mem_inf.1 hx).1, P ⊓ K, le_rfl, ?_, (Subgroup.mem_inf.1 hx).2⟩
    have hE := alt6_isElemAbelian_of_iso K P φ hQ
    have h2 := le_pRank_three_of_elemAbelian hE 2 (hP9.trans (by norm_num))
    omega

theorem alt6_normalizer_psi {X : Type} [Group X] [Finite X] (K : Subgroup X) (hKn : K.Normal)
    (φ : K ≃* alternatingGroup (Fin 6)) {R : Subgroup X} (hRK : R ≤ K) (k : K) :
    (k : X) ∈ Subgroup.normalizer (R : Set X) ↔
      (alternatingGroup (Fin 6)).subtype (φ k) ∈
        Subgroup.normalizer
          ((((R.subgroupOf K).map ((alternatingGroup (Fin 6)).subtype.comp φ.toMonoidHom)) :
            Subgroup (Equiv.Perm (Fin 6))) : Set (Equiv.Perm (Fin 6))) := by
  set ψ : K →* Equiv.Perm (Fin 6) := (alternatingGroup (Fin 6)).subtype.comp φ.toMonoidHom
    with hψ
  show (k : X) ∈ Subgroup.normalizer (R : Set X) ↔
    ψ k ∈ Subgroup.normalizer ((((R.subgroupOf K).map ψ) : Subgroup (Equiv.Perm (Fin 6))) :
      Set (Equiv.Perm (Fin 6)))
  have hψinj : Function.Injective ψ := fun a b h => φ.injective (Subtype.ext h)
  have hψA : ∀ s : K, ψ s ∈ alternatingGroup (Fin 6) := fun s => (φ s).2
  have hmemRp : ∀ s : K, ψ s ∈ (R.subgroupOf K).map ψ ↔ (s : X) ∈ R := by
    intro s
    constructor
    · intro h
      obtain ⟨t, ht, he⟩ := Subgroup.mem_map.1 h
      have hts : t = s := hψinj he
      subst hts
      exact Subgroup.mem_subgroupOf.1 ht
    · intro h
      exact Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.2 h)
  have hconj : ∀ s : K, ψ k * ψ s * (ψ k)⁻¹ = ψ (k * s * k⁻¹) := by
    intro s
    rw [map_mul, map_mul, map_inv]
  have hRpA : ∀ y ∈ (R.subgroupOf K).map ψ, y ∈ alternatingGroup (Fin 6) := by
    intro y hy
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact hψA t
  have hconjA : ∀ g : Equiv.Perm (Fin 6),
      g ∈ alternatingGroup (Fin 6) ↔ ψ k * g * (ψ k)⁻¹ ∈ alternatingGroup (Fin 6) := by
    intro g
    have hk := hψA k
    constructor
    · intro hg
      exact mul_mem (mul_mem hk hg) (inv_mem hk)
    · intro hg
      have e : g = (ψ k)⁻¹ * (ψ k * g * (ψ k)⁻¹) * ψ k := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hk) hg) hk
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h z
    by_cases hz : z ∈ alternatingGroup (Fin 6)
    · obtain ⟨s, hs⟩ : ∃ s : K, ψ s = z := ⟨φ.symm ⟨z, hz⟩, by simp [hψ]⟩
      subst hs
      rw [hconj s, hmemRp, hmemRp]
      simpa using h (s : X)
    · exact ⟨fun hzR => absurd (hRpA z hzR) hz,
        fun hc => absurd (hRpA _ hc) (fun hA => hz ((hconjA z).2 hA))⟩
  · intro h y
    by_cases hyK : y ∈ K
    · have e1 : y ∈ R ↔ ψ ⟨y, hyK⟩ ∈ (R.subgroupOf K).map ψ := (hmemRp ⟨y, hyK⟩).symm
      have e2 : ψ ⟨y, hyK⟩ ∈ (R.subgroupOf K).map ψ ↔
          ψ k * ψ ⟨y, hyK⟩ * (ψ k)⁻¹ ∈ (R.subgroupOf K).map ψ := h _
      have e3 : ψ k * ψ ⟨y, hyK⟩ * (ψ k)⁻¹ = ψ (k * ⟨y, hyK⟩ * k⁻¹) := hconj ⟨y, hyK⟩
      have e4 : ψ (k * ⟨y, hyK⟩ * k⁻¹) ∈ (R.subgroupOf K).map ψ ↔
          ((k : X) * y * (k : X)⁻¹) ∈ R := hmemRp _
      rw [e3] at e2
      exact e1.trans (e2.trans e4)
    · have hn1 : y ∉ R := fun hh => hyK (hRK hh)
      have hn2 : (k : X) * y * (k : X)⁻¹ ∉ R := by
        intro hh
        apply hyK
        have hc := hKn.conj_mem _ (hRK hh) (k : X)⁻¹
        have e : (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * (k : X)⁻¹⁻¹ = y := by group
        rw [e] at hc
        exact hc
      exact ⟨fun hh => absurd hh hn1, fun hh => absurd hh hn2⟩

theorem alt6_PA_iff_image : ∀ g : Equiv.Perm (Fin 6), alt6_PA g ↔
    (({0, 1, 2} : Finset (Fin 6)).image g = {0, 1, 2} ∨
      ({0, 1, 2} : Finset (Fin 6)).image g = ({0, 1, 2} : Finset (Fin 6))ᶜ) := by
  decide +kernel

theorem alt6_partition_iff {X : Type} [Group X] [Finite X] (K P : Subgroup X) (hKn : K.Normal)
    (φ : K ≃* alternatingGroup (Fin 6))
    (hQ : (Subgroup.map φ.toMonoidHom ((P ⊓ K).subgroupOf K)).map (alternatingGroup (Fin 6)).subtype
      = alt6_Q0) (k : K) :
    (k : X) ∈ gammaCore 3 1 K (P ⊓ K) ↔
      (({0, 1, 2} : Finset (Fin 6)).image (φ k : Equiv.Perm (Fin 6)) = {0, 1, 2} ∨
        ({0, 1, 2} : Finset (Fin 6)).image (φ k : Equiv.Perm (Fin 6)) =
          ({0, 1, 2} : Finset (Fin 6))ᶜ) := by
  have hQψ : ((P ⊓ K).subgroupOf K).map ((alternatingGroup (Fin 6)).subtype.comp φ.toMonoidHom)
      = alt6_Q0 := by
    rw [← hQ, Subgroup.map_map]
  rw [alt6_gammaCore_eq K P hKn φ hQ, Subgroup.mem_inf]
  refine (and_iff_right k.2).trans ?_
  rw [alt6_normalizer_psi K hKn φ (inf_le_right : P ⊓ K ≤ K) k, hQψ]
  constructor
  · intro hN
    have hS := alt6_normalizer_le_stab0 alt6_Q0 le_rfl alt6_Q0_ne_bot _ (φ k).2 hN
    rw [alt6_mem_Stab0_iff] at hS
    exact (alt6_PA_iff_image _).1 hS.2
  · intro hS
    have hS' : (φ k : Equiv.Perm (Fin 6)) ∈ alt6_Stab0 :=
      (alt6_mem_Stab0_iff _).2
        ⟨Equiv.Perm.mem_alternatingGroup.1 (φ k).2, (alt6_PA_iff_image _).2 hS⟩
    rw [alt6_stab0_eq] at hS'
    exact (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 alt6_jPerm_mem.2)) hS'

theorem alt6_gammaCore_lt {X : Type} [Group X] [Finite X] (K P : Subgroup X) (hKn : K.Normal)
    (φ : K ≃* alternatingGroup (Fin 6))
    (hQ : (Subgroup.map φ.toMonoidHom ((P ⊓ K).subgroupOf K)).map (alternatingGroup (Fin 6)).subtype
      = alt6_Q0) :
    gammaCore 3 1 K (P ⊓ K) < K := by
  have hK : gammaCore 3 1 K (P ⊓ K) ≤ K := by
    unfold gammaCore
    rw [Subgroup.closure_le]
    rintro x ⟨hxK, -⟩
    exact hxK
  refine lt_of_le_of_ne hK ?_
  intro heq
  have hgA : (Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 6)) ∈ alternatingGroup (Fin 6) :=
    Equiv.Perm.mem_alternatingGroup.2 (by decide)
  obtain ⟨k0, hk0φ⟩ : ∃ k0 : K, φ k0 = ⟨Equiv.swap 0 1 * Equiv.swap 1 3, hgA⟩ :=
    ⟨φ.symm ⟨_, hgA⟩, φ.apply_symm_apply _⟩
  have hk0 : (k0 : X) ∈ gammaCore 3 1 K (P ⊓ K) := by
    rw [heq]
    exact k0.2
  rw [alt6_partition_iff K P hKn φ hQ k0] at hk0
  have hval : (φ k0 : Equiv.Perm (Fin 6)) = Equiv.swap 0 1 * Equiv.swap 1 3 := by
    rw [hk0φ]
  rw [hval] at hk0
  revert hk0
  decide +kernel

theorem alt6_gammaCore_maximal {X : Type} [Group X] [Finite X] (K P : Subgroup X)
    (hKn : K.Normal) (φ : K ≃* alternatingGroup (Fin 6))
    (hQ : (Subgroup.map φ.toMonoidHom ((P ⊓ K).subgroupOf K)).map (alternatingGroup (Fin 6)).subtype
      = alt6_Q0) :
    ∀ H : Subgroup X, gammaCore 3 1 K (P ⊓ K) < H → H ≤ K → H = K := by
  intro H hlt hHK
  set ψ : K →* Equiv.Perm (Fin 6) := (alternatingGroup (Fin 6)).subtype.comp φ.toMonoidHom
    with hψ
  have hψinj : Function.Injective ψ := fun a b h => φ.injective (Subtype.ext h)
  have hψapp : ∀ k : K, ψ k = (φ k : Equiv.Perm (Fin 6)) := fun k => rfl
  have hmemM : ∀ s : K, ψ s ∈ (H.subgroupOf K).map ψ ↔ (s : X) ∈ H := by
    intro s
    constructor
    · intro h
      obtain ⟨t, ht, he⟩ := Subgroup.mem_map.1 h
      have hts : t = s := hψinj he
      subst hts
      exact Subgroup.mem_subgroupOf.1 ht
    · intro h
      exact Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.2 h)
  have hMA : (H.subgroupOf K).map ψ ≤ alternatingGroup (Fin 6) := by
    rintro y hy
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact (φ t).2
  have hstabM : alt6_Stab0 ≤ (H.subgroupOf K).map ψ := by
    intro g hg
    obtain ⟨hs, hP⟩ := (alt6_mem_Stab0_iff g).1 hg
    have hgA : g ∈ alternatingGroup (Fin 6) := Equiv.Perm.mem_alternatingGroup.2 hs
    obtain ⟨k, hk⟩ : ∃ k : K, φ k = ⟨g, hgA⟩ :=
      ⟨φ.symm ⟨g, hgA⟩, φ.apply_symm_apply _⟩
    have hΓ : (k : X) ∈ gammaCore 3 1 K (P ⊓ K) :=
      (alt6_partition_iff K P hKn φ hQ k).2 (by
        rw [hk]
        exact (alt6_PA_iff_image g).1 hP)
    have hψk : ψ k = g := by rw [hψapp, hk]
    rw [← hψk]
    exact (hmemM k).2 (hlt.le hΓ)
  have hne : alt6_Stab0 ≠ (H.subgroupOf K).map ψ := by
    obtain ⟨h, hHmem, hhnΓ⟩ : ∃ h ∈ H, h ∉ gammaCore 3 1 K (P ⊓ K) := by
      by_contra hc
      push Not at hc
      exact not_le_of_gt hlt (fun x hx => hc x hx)
    have hhK : h ∈ K := hHK hHmem
    have hnotS : ψ ⟨h, hhK⟩ ∉ alt6_Stab0 := by
      intro hS
      apply hhnΓ
      rw [alt6_mem_Stab0_iff] at hS
      exact (alt6_partition_iff K P hKn φ hQ ⟨h, hhK⟩).2 ((alt6_PA_iff_image _).1 hS.2)
    intro heq
    apply hnotS
    rw [heq]
    exact (hmemM ⟨h, hhK⟩).2 hHmem
  have hMfull : (H.subgroupOf K).map ψ = alternatingGroup (Fin 6) :=
    alt6_stab0_maximal _ (lt_of_le_of_ne hstabM hne) hMA
  apply le_antisymm hHK
  intro x hx
  have hmem : ψ ⟨x, hx⟩ ∈ (H.subgroupOf K).map ψ := by
    rw [hMfull]
    exact (φ ⟨x, hx⟩).2
  obtain ⟨t, ht, he⟩ := Subgroup.mem_map.1 hmem
  have htk : t = ⟨x, hx⟩ := hψinj he
  have hxt := Subgroup.mem_subgroupOf.1 ht
  rw [htk] at hxt
  exact hxt

theorem alt6_gammaCore_decomp_of {X : Type} [Group X] [Finite X] (K P : Subgroup X)
    (hKn : K.Normal) (φ : K ≃* alternatingGroup (Fin 6))
    (hQ : (Subgroup.map φ.toMonoidHom ((P ⊓ K).subgroupOf K)).map (alternatingGroup (Fin 6)).subtype
      = alt6_Q0)
    (kj : K) (hkj : φ kj = ⟨alt6_j, alt6_jPerm_mem.1⟩) :
    gammaCore 3 1 K (P ⊓ K) = (P ⊓ K) ⊔ Subgroup.zpowers (kj : X) := by
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : K →* Equiv.Perm (Fin 6),
      ψ = (alternatingGroup (Fin 6)).subtype.comp φ.toMonoidHom := ⟨_, rfl⟩
  have hψapp : ∀ k : K, ψ k = (φ k : Equiv.Perm (Fin 6)) := fun k => by
    rw [hψdef]
    rfl
  have hψinj : Function.Injective ψ := by
    intro a b h
    apply φ.injective
    apply Subtype.ext
    rw [← hψapp a, ← hψapp b]
    exact h
  have hQψ : ((P ⊓ K).subgroupOf K).map ψ = alt6_Q0 := by
    rw [hψdef, ← hQ, Subgroup.map_map]
  have hψkj : ψ kj = alt6_j := by
    rw [hψapp, hkj]
  have hMap : Subgroup.map ψ ((P ⊓ K).subgroupOf K ⊔ Subgroup.zpowers kj) = alt6_Stab0 := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hψkj, hQψ]
    exact alt6_stab0_eq.symm
  have hcomap : Subgroup.comap ψ alt6_Stab0 = (P ⊓ K).subgroupOf K ⊔ Subgroup.zpowers kj := by
    rw [← hMap]
    exact Subgroup.comap_map_eq_self_of_injective hψinj _
  have hmemK : ∀ k : K, k ∈ (P ⊓ K).subgroupOf K ⊔ Subgroup.zpowers kj ↔ ψ k ∈ alt6_Stab0 := by
    intro k
    rw [← hcomap]
    exact Iff.rfl
  have hsubX : (P ⊓ K).subgroupOf K ⊔ Subgroup.zpowers kj ≤
      Subgroup.comap K.subtype ((P ⊓ K) ⊔ Subgroup.zpowers (kj : X)) :=
    sup_le (fun y hy => Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hy))
      (Subgroup.zpowers_le.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  have hΓK : gammaCore 3 1 K (P ⊓ K) ≤ K := by
    rw [alt6_gammaCore_eq K P hKn φ hQ]
    exact inf_le_left
  have hStab : ∀ k : K, (k : X) ∈ gammaCore 3 1 K (P ⊓ K) → ψ k ∈ alt6_Stab0 := by
    intro k hk
    rw [alt6_mem_Stab0_iff, hψapp]
    exact ⟨Equiv.Perm.mem_alternatingGroup.1 (φ k).2,
      (alt6_PA_iff_image _).2 ((alt6_partition_iff K P hKn φ hQ k).1 hk)⟩
  apply le_antisymm
  · intro x hx
    have hxK : x ∈ K := hΓK hx
    have hkmem : (⟨x, hxK⟩ : K) ∈ (P ⊓ K).subgroupOf K ⊔ Subgroup.zpowers kj :=
      (hmemK ⟨x, hxK⟩).2 (hStab ⟨x, hxK⟩ hx)
    exact hsubX hkmem
  · apply sup_le
    · rw [alt6_gammaCore_eq K P hKn φ hQ]
      exact le_inf inf_le_right Subgroup.le_normalizer
    · apply Subgroup.zpowers_le.2
      apply (alt6_partition_iff K P hKn φ hQ kj).2
      rw [hkj]
      exact (alt6_PA_iff_image _).1 alt6_j_PA

theorem alt6_gammaCore_decomp {X : Type} [Group X] [Finite X] (K P : Subgroup X)
    (hKn : K.Normal) (φ : K ≃* alternatingGroup (Fin 6))
    (hQ : (Subgroup.map φ.toMonoidHom ((P ⊓ K).subgroupOf K)).map (alternatingGroup (Fin 6)).subtype
      = alt6_Q0) :
    gammaCore 3 1 K (P ⊓ K) =
      (P ⊓ K) ⊔ Subgroup.zpowers ((φ.symm ⟨alt6_j, alt6_jPerm_mem.1⟩ : K) : X) :=
  alt6_gammaCore_decomp_of K P hKn φ hQ (φ.symm ⟨alt6_j, alt6_jPerm_mem.1⟩)
    (φ.apply_symm_apply _)

theorem alt6_actsIrr_transport_of {X : Type} [Group X] [Finite X] (K P : Subgroup X)
    (hKn : K.Normal) (φ : K ≃* alternatingGroup (Fin 6))
    (hQ : (Subgroup.map φ.toMonoidHom ((P ⊓ K).subgroupOf K)).map (alternatingGroup (Fin 6)).subtype
      = alt6_Q0)
    (kj : K) (hkj : φ kj = ⟨alt6_j, alt6_jPerm_mem.1⟩) :
    ActsIrr (Subgroup.zpowers (kj : X)) (P ⊓ K) := by
  intro W hW hN
  have hWK : W ≤ K := hW.trans inf_le_right
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : K →* Equiv.Perm (Fin 6),
      ψ = (alternatingGroup (Fin 6)).subtype.comp φ.toMonoidHom := ⟨_, rfl⟩
  have hψapp : ∀ k : K, ψ k = (φ k : Equiv.Perm (Fin 6)) := fun k => by
    rw [hψdef]
    rfl
  have hψinj : Function.Injective ψ := by
    intro a b h
    apply φ.injective
    apply Subtype.ext
    rw [← hψapp a, ← hψapp b]
    exact h
  have hQψ : ((P ⊓ K).subgroupOf K).map ψ = alt6_Q0 := by
    rw [hψdef, ← hQ, Subgroup.map_map]
  have hW' : (W.subgroupOf K).map ψ ≤ alt6_Q0 := by
    rintro y hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← hQψ]
    exact Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.2 (hW (Subgroup.mem_subgroupOf.1 ht)))
  have hjN : alt6_j ∈ Subgroup.normalizer
      ((((W.subgroupOf K).map ψ) : Subgroup (Equiv.Perm (Fin 6))) : Set (Equiv.Perm (Fin 6))) := by
    have h1 := (alt6_normalizer_psi K hKn φ hWK kj).1 (hN (Subgroup.mem_zpowers _))
    rw [← hψdef] at h1
    rw [hkj] at h1
    exact h1
  have hNW : Subgroup.zpowers alt6_j ≤ Subgroup.normalizer
      ((((W.subgroupOf K).map ψ) : Subgroup (Equiv.Perm (Fin 6))) : Set (Equiv.Perm (Fin 6))) :=
    Subgroup.zpowers_le.2 hjN
  rcases alt6_actsIrr _ hW' hNW with hbot | htop
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxK : x ∈ K := hWK hx
    have hmem : ψ ⟨x, hxK⟩ ∈ (W.subgroupOf K).map ψ :=
      Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.2 hx)
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : (⟨x, hxK⟩ : K) = 1 := hψinj (by rw [hmem, map_one])
    exact congrArg Subtype.val h1
  · right
    have heq : W.subgroupOf K = (P ⊓ K).subgroupOf K := by
      apply Subgroup.map_injective hψinj
      rw [htop, hQψ]
    apply le_antisymm hW
    intro x hx
    have hxK : x ∈ K := hx.2
    have hmem : (⟨x, hxK⟩ : K) ∈ (P ⊓ K).subgroupOf K := Subgroup.mem_subgroupOf.2 hx
    rw [← heq] at hmem
    exact Subgroup.mem_subgroupOf.1 hmem

theorem alt6_actsIrr_transport {X : Type} [Group X] [Finite X] (K P : Subgroup X)
    (hKn : K.Normal) (φ : K ≃* alternatingGroup (Fin 6))
    (hQ : (Subgroup.map φ.toMonoidHom ((P ⊓ K).subgroupOf K)).map (alternatingGroup (Fin 6)).subtype
      = alt6_Q0) :
    ActsIrr (Subgroup.zpowers ((φ.symm ⟨alt6_j, alt6_jPerm_mem.1⟩ : K) : X)) (P ⊓ K) :=
  alt6_actsIrr_transport_of K P hKn φ hQ (φ.symm ⟨alt6_j, alt6_jPerm_mem.1⟩)
    (φ.apply_symm_apply _)

theorem gls3ConclusionPlus_of_alt6 {X : Type} [Group X] [Finite X] (K : Subgroup X) (P : Sylow 3 X)
    (hKn : K.Normal) (hKc : Subgroup.centralizer (K : Set X) = ⊥)
    (e : K ≃* alternatingGroup (Fin 6)) : Gls3ConclusionPlus X K (P : Subgroup X) := by
  have hX : Nat.card X ∣ 1440 := alt6_card_dvd K hKn e hKc
  obtain ⟨hPK, hP9⟩ := alt6_sylow_le K hKn e hX P
  have hPK' : (P : Subgroup X) ⊓ K = (P : Subgroup X) := inf_eq_left.2 hPK
  have hP9' : Nat.card ((P : Subgroup X) ⊓ K : Subgroup X) = 9 := by
    rw [hPK']
    exact hP9
  obtain ⟨φ, hQ⟩ := alt6_exists_iso K (P : Subgroup X) e hP9'
  have hidx : K.index ∣ 4 := alt6_index_K_dvd K e hX
  have hEA : IsElemAbelian 3 ((P : Subgroup X) ⊓ K) :=
    alt6_isElemAbelian_of_iso K (P : Subgroup X) φ hQ
  have hGam := alt6_gammaCore_eq K (P : Subgroup X) hKn φ hQ
  refine ⟨alt6_gammaCore_lt K (P : Subgroup X) hKn φ hQ,
    alt6_gammaCore_maximal K (P : Subgroup X) hKn φ hQ, ?_⟩
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
  refine ⟨⟨φ, ({0, 1, 2} : Finset (Fin 6)), by decide,
    fun k => alt6_partition_iff K (P : Subgroup X) hKn φ hQ k⟩, ?_, hEA, hP9', hGam, ?_⟩
  · exact fun h3 => absurd (dvd_trans h3 hidx) (by norm_num)
  · exact ⟨Subgroup.zpowers ((φ.symm ⟨alt6_j, alt6_jPerm_mem.1⟩ : K) : X), inferInstance,
      alt6_gammaCore_decomp K (P : Subgroup X) hKn φ hQ,
      alt6_actsIrr_transport K (P : Subgroup X) hKn φ hQ⟩

theorem gls3PlusCase_alternating_six (h5 : 5 ≤ 6) : Gls3PlusCase (.alternating 6 h5) := by
  unfold Gls3PlusCase
  intro X _ _ _ K hKn _ _ hiso hKc P _ _
  obtain ⟨e⟩ := hiso
  have e' : ↥K ≃* ↥(alternatingGroup (Fin 6)) := e
  exact gls3ConclusionPlus_of_alt6 K P hKn hKc e'

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

end
