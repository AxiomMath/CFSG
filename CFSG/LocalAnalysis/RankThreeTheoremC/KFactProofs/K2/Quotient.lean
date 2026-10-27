module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Defs
import CFSG.GroupTheory.CoprimeQuotientNormalizer
import CFSG.GH74.Constrained
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Signal
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28Generic
import CFSG.HardMathSupport.Timmesfeld.Proving.ElemAbelianSubgroup
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

section Cards

variable {G : Type} [Group G] [Finite G] {Y Q : Subgroup G}

theorem normalizer_map_le_map_normalizer (O : Subgroup G) [O.Normal] (hO : ¬ 3 ∣ Nat.card O)
    {S : Subgroup G} (hS : IsPGroup 3 S) :
    normalizer ((S.map (QuotientGroup.mk' O) : Subgroup (G ⧸ O)) : Set (G ⧸ O)) ≤
      (normalizer (S : Set G)).map (QuotientGroup.mk' O) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (CFSG.GroupTheory.normal_coprime_quotient_normalizer 3 O hO S hS).ge

theorem qb_inf_eq_bot_of_pGroup {p : ℕ} (hp : p.Prime) {H : Type*} [Group H] [Finite H]
    {E Y : Subgroup H} (k : ℕ) (hk : Nat.card E = p ^ k) (hY : ¬ p ∣ Nat.card ↥Y) :
    E ⊓ Y = ⊥ := by
  have hd1 : Nat.card ↥(E ⊓ Y) ∣ p ^ k := hk ▸ Subgroup.card_dvd_of_le inf_le_left
  have hd2 : Nat.card ↥(E ⊓ Y) ∣ Nat.card ↥Y :=
    Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime (Nat.card ↥(E ⊓ Y)) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => hY (h.trans hd2))).symm
  exact Subgroup.eq_bot_of_card_eq _
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) hd1)

theorem qb_pRank_map_eq_of_kernel {p : ℕ} (hp : p.Prime) {H H' : Type*} [Group H] [Finite H]
    [Group H'] [Finite H'] (f : H →* H') (A : Subgroup H)
    (hY : ¬ p ∣ Nat.card ↥(A ⊓ f.ker)) :
    CFSG.Open.pRank p (A.map f) = CFSG.Open.pRank p A := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hker : ∀ (E : Subgroup H), E ≤ A → ∀ k : ℕ, Nat.card E = p ^ k → E ⊓ f.ker = ⊥ := by
    intro E hEA k hk
    have h := qb_inf_eq_bot_of_pGroup hp k hk hY
    have hEY : E ⊓ (A ⊓ f.ker) = E ⊓ f.ker := by
      rw [← inf_assoc, inf_eq_left.2 hEA]
    rwa [hEY] at h
  have hcardmap : ∀ (E : Subgroup H), E ⊓ f.ker = ⊥ → Nat.card ↥(E.map f) = Nat.card ↥E := by
    intro E hE
    have hinj : Function.Injective (f.comp E.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : (x : H) ∈ E ⊓ f.ker := Subgroup.mem_inf.2 ⟨x.2, hx⟩
      rw [hE, Subgroup.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      exact Subtype.ext hx'
    have hmap : E.map f = (⊤ : Subgroup ↥E).map (f.comp E.subtype) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
      · rintro ⟨x, -, rfl⟩
        exact ⟨x, x.2, rfl⟩
    rw [hmap, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  apply le_antisymm
  ·
    obtain ⟨E', hE'sub, hE'ab, hE'card⟩ := CFSG.SectionRank.exists_pRank hp1 (A.map f)
    have hE'comm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := fun x hx y hy => by
      have := hE'ab.1.is_comm.comm (⟨x, hx⟩ : ↥E') ⟨y, hy⟩
      exact congrArg Subtype.val this
    have hE'exp : ∀ x ∈ E', x ^ p = 1 := hE'ab.2
    set P : Subgroup H := A ⊓ Subgroup.comap f E' with hP
    have hPA : P ≤ A := inf_le_left
    have hfE : ∀ x ∈ P, f x ∈ E' := fun x hx => Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hx).2
    set g : ↥P →* H' := f.comp P.subtype with hg
    have hrange : g.range = E' := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hy
        rw [← hx]
        exact hfE x.1 x.2
      · intro hy
        obtain ⟨a, ha, hfa⟩ := Subgroup.mem_map.1 (hE'sub hy)
        have haP : a ∈ P := Subgroup.mem_inf.2 ⟨ha, by rw [Subgroup.mem_comap, hfa]; exact hy⟩
        exact MonoidHom.mem_range.2 ⟨⟨a, haP⟩, by simp [hg, hfa]⟩
    have hPdvd : p ^ CFSG.Open.pRank p (A.map f) ∣ Nat.card ↥P := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hrange, hE'card]
      exact dvd_mul_right _ _
    obtain ⟨K, hKcard, -⟩ := Sylow.exists_subgroup_card_pow_prime_le (n := 0) p hPdvd ⊥
      (by simp) (Nat.zero_le _)
    set S : Subgroup H := K.map P.subtype with hS
    have hSP : S ≤ P := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hScard : Nat.card ↥S = p ^ CFSG.Open.pRank p (A.map f) := by
      rw [hS, Subgroup.card_map_of_injective P.subtype_injective, hKcard]
    have hSA : S ≤ A := hSP.trans hPA
    have hSker : S ⊓ f.ker = ⊥ := hker S hSA _ hScard
    have hSfE : ∀ x ∈ S, f x ∈ E' := fun x hx => hfE x (hSP hx)
    have hSab : IsElemAbelian p S := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · have hc : ((a : H) * b) * ((b : H) * a)⁻¹ ∈ S ⊓ f.ker := by
          refine Subgroup.mem_inf.2
            ⟨S.mul_mem (S.mul_mem a.2 b.2) (S.inv_mem (S.mul_mem b.2 a.2)), ?_⟩
          rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul]
          rw [hE'comm _ (hSfE a a.2) _ (hSfE b b.2)]
          group
        rw [hSker, Subgroup.mem_bot, mul_inv_eq_one] at hc
        exact Subtype.ext hc
      · have hxp : f (x ^ p) = 1 := by
          rw [map_pow]
          exact hE'exp _ (hSfE x hx)
        have hm : x ^ p ∈ S ⊓ f.ker :=
          Subgroup.mem_inf.2 ⟨S.pow_mem hx p, (MonoidHom.mem_ker).2 hxp⟩
        rw [hSker, Subgroup.mem_bot] at hm
        exact hm
    exact CFSG.SectionRank.le_pRank hp1 hSA hSab hScard
  ·
    obtain ⟨E, hEA, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1 A
    have hE := hker E hEA _ hEcard
    have hmapcard := hcardmap E hE
    exact CFSG.SectionRank.le_pRank hp1 (Subgroup.map_mono hEA)
      (CFSG.SectionRank.isElemAbelian_map hEab f) (by rw [hmapcard, hEcard])

theorem pRank_map_eq_of_coprime_ker {H : Type} [Group H] [Finite H] (π : G →* H)
    {S : Subgroup G} {p : ℕ} (hp : p.Prime) (hS : ¬ p ∣ Nat.card ↥(S ⊓ π.ker)) :
    CFSG.Open.pRank p (S.map π) = CFSG.Open.pRank p S :=
  qb_pRank_map_eq_of_kernel hp π S hS

theorem centralizer_map_quotient (O : Subgroup G) [O.Normal] (hO : ¬ 3 ∣ Nat.card O) {x : G}
    (hx : orderOf x = 3) :
    centralizer ({QuotientGroup.mk' O x} : Set (G ⧸ O)) =
      (centralizer ({x} : Set G)).map (QuotientGroup.mk' O) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.GH74.centralizer_singleton_quotient_eq_map 3 O
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hO) ⟨1, by rw [hx, pow_one]⟩

theorem primeCore_le (h : K2Setup G Y Q) : primeComplementCore (G := G) 3 ≤ Y := by
  have hO3 : ¬ 3 ∣ Nat.card (primeComplementCore (G := G) 3) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (primeComplementCore_coprime 3)
  obtain ⟨E, hEQ, hE, hE27⟩ := CFSG.AGLEmbedding.KFactProofs.G28.exists_elemAbelian_27 h.rank
  obtain ⟨U, hUE, hU, hU9⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.exists_elemAbelian_subgroup_card_pow
      (p := 3) (k := 3) (m := 2) Nat.prime_three hE (by norm_num) (by rw [hE27]; norm_num)
  refine CFSG.LocalAnalysis.RankThreeTheoremC.le_of_plane_centralizers_le hU
    (by rw [hU9]; norm_num) ?_ hO3 ?_
  · rw [Subgroup.normalizer_eq_top]
    exact le_top
  · intro u hu hu1
    have huE : u ∈ E := hUE hu
    have hu3 : u ^ 3 = 1 := hE.2 u huE
    have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
    have hSE : Subgroup.zpowers u ≤ E := Subgroup.zpowers_le.2 huE
    have hzp : IsElemAbelian 3 (Subgroup.zpowers u) := CFSG.Open.isElemAbelian_zpowers hu3
    have hcard : Nat.card (Subgroup.zpowers u) = 3 ^ 1 := by
      rw [Nat.card_zpowers, hord, pow_one]
    have hS : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers u) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_rfl hzp hcard
    refine le_trans ?_ (h.y2 E hEQ hE hE27 (Subgroup.zpowers u) hSE hS)
    calc centralizer ({u} : Set G)
        = centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
          rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      _ ≤ normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) :=
          Subgroup.centralizer_le_normalizer _

theorem primeComplementCore_bar : primeComplementCore (G := Bar G) 3 = ⊥ :=
  primeComplementCore_quotient_eq_bot 3

end Cards

section Cards

variable {G : Type} [Group G] [Finite G] {Y Q : Subgroup G}

theorem qs_not_dvd_core : ¬ 3 ∣ Nat.card (primeComplementCore (G := G) 3) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (primeComplementCore_coprime 3)

theorem qs_ker : (barMk G).ker = primeComplementCore (G := G) 3 :=
  QuotientGroup.ker_mk' _

theorem qs_eq_one_of_mem {x : G} (hQ : IsPGroup 3 Q) (hxQ : x ∈ Q)
    (hxO : x ∈ primeComplementCore (G := G) 3) : x = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨x, hxQ⟩
  have hk' : x ^ 3 ^ k = 1 := congrArg Subtype.val hk
  have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf x ∣ Nat.card (primeComplementCore (G := G) 3) :=
    Subgroup.orderOf_dvd_natCard _ hxO
  have hcop : Nat.Coprime (Nat.card (primeComplementCore (G := G) 3)) (3 ^ k) :=
    (primeComplementCore_coprime 3).symm.pow_right k
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)

theorem qs_injOn (hQ : IsPGroup 3 Q) : Set.InjOn (barMk G) (Q : Set G) := by
  intro x hx y hy hxy
  have hxy' : (x : Bar G) = (y : Bar G) := hxy
  have hmem : x⁻¹ * y ∈ primeComplementCore (G := G) 3 := QuotientGroup.eq.mp hxy'
  have hQmem : x⁻¹ * y ∈ Q := Q.mul_mem (Q.inv_mem hx) hy
  exact inv_mul_eq_one.mp (qs_eq_one_of_mem hQ hQmem hmem)

theorem qs_card_map (hQ : IsPGroup 3 Q) {T : Subgroup G} (hT : T ≤ Q) :
    Nat.card (T.map (barMk G)) = Nat.card T := by
  have hinj : Set.InjOn (barMk G) (T : Set G) := (qs_injOn hQ).mono hT
  have := Nat.card_image_of_injOn hinj
  rw [← Subgroup.coe_map] at this
  exact this

theorem qs_inf_ker (hQ : IsPGroup 3 Q) {T : Subgroup G} (hT : T ≤ Q) :
    T ⊓ (barMk G).ker = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hxT, hxK⟩
  rw [qs_ker] at hxK
  exact qs_eq_one_of_mem hQ (hT hxT) hxK

theorem qs_pRank (hQ : IsPGroup 3 Q) {T : Subgroup G} (hT : T ≤ Q) :
    CFSG.Open.pRank 3 (T.map (barMk G)) = CFSG.Open.pRank 3 T := by
  refine pRank_map_eq_of_coprime_ker (barMk G) Nat.prime_three ?_
  rw [qs_inf_ker hQ hT, Subgroup.card_bot]
  omega

theorem qs_preimage {T : Subgroup G} {Sb : Subgroup (Bar G)}
    (hSb : Sb ≤ T.map (barMk G)) :
    ∃ S : Subgroup G, S ≤ T ∧ S.map (barMk G) = Sb := by
  refine ⟨T ⊓ Sb.comap (barMk G), inf_le_left, ?_⟩
  ext y
  constructor
  · rintro ⟨x, ⟨_, hxS⟩, rfl⟩
    exact hxS
  · intro hy
    obtain ⟨x, hxT, hx⟩ := hSb hy
    exact ⟨x, ⟨hxT, by show (barMk G) x ∈ Sb; rw [hx]; exact hy⟩, hx⟩

theorem qs_elemAbelian (hQ : IsPGroup 3 Q) {E : Subgroup G} (hE : E ≤ Q)
    (hEb : IsElemAbelian 3 (E.map (barMk G))) : IsElemAbelian 3 E := by
  have hinj : Set.InjOn (barMk G) (E : Set G) := (qs_injOn hQ).mono hE
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have hab : (a : G) * b = b * a := by
      refine hinj (E.mul_mem a.2 b.2) (E.mul_mem b.2 a.2) ?_
      rw [map_mul, map_mul]
      exact hEb.comm (Subgroup.mem_map_of_mem _ a.2) (Subgroup.mem_map_of_mem _ b.2)
    exact hab
  · refine hinj (E.pow_mem hx 3) E.one_mem ?_
    rw [map_pow, map_one]
    exact hEb.2 _ (Subgroup.mem_map_of_mem _ hx)

theorem K2Setup.quotient (h : K2Setup G Y Q) :
    K2Setup (Bar G) (Y.map (barMk G)) (Q.map (barMk G)) := by
  have hO : ¬ 3 ∣ Nat.card (primeComplementCore (G := G) 3) := qs_not_dvd_core
  have hP : IsPGroup 3 Q := h.pgroup
  have hOY : primeComplementCore (G := G) 3 ≤ Y := primeCore_le h
  refine
    { catalog := h.catalog.quotient (primeComplementCore (G := G) 3)
      pgroup := h.pgroup.map (barMk G)
      index := ?_
      rank := ?_
      elt := ?_
      proper := ?_
      le := Subgroup.map_mono h.le
      y1 := ?_
      y2 := ?_ }
  · exact fun hdvd =>
      h.index (hdvd.trans (Subgroup.index_map_dvd Q (QuotientGroup.mk'_surjective _)))
  · rw [qs_pRank hP le_rfl]
    exact h.rank
  · obtain ⟨x, hx3, hxr⟩ := h.elt
    have hxO : x ∉ primeComplementCore (G := G) 3 := fun hxO => by
      have := Subgroup.orderOf_dvd_natCard (primeComplementCore (G := G) 3) hxO
      rw [hx3] at this
      exact hO this
    have hord : orderOf (barMk G x) = 3 := by
      have hdvd : orderOf (barMk G x) ∣ 3 := by
        have := orderOf_map_dvd (barMk G) x
        rwa [hx3] at this
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
      · exfalso
        apply hxO
        rw [orderOf_eq_one_iff] at h1
        have hk : x ∈ (barMk G).ker := h1
        rwa [qs_ker] at hk
      · exact h3
    refine ⟨barMk G x, hord, ?_⟩
    rw [centralizer_map_quotient (primeComplementCore (G := G) 3) hO hx3]
    rw [pRank_map_eq_of_coprime_ker (barMk G) Nat.prime_three ?_]
    · exact hxr
    · intro hdvd
      apply hO
      exact hdvd.trans (Subgroup.card_dvd_of_le (inf_le_right.trans (qs_ker (G := G)).le))
  · intro htop
    apply h.proper
    have h1 : Y ⊔ (barMk G).ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, htop, Subgroup.comap_top]
    rwa [qs_ker, sup_eq_left.mpr hOY] at h1
  · intro Sb hSb hrk
    obtain ⟨S, hSQ, hSmap⟩ := qs_preimage (T := Q) hSb
    have hSrk : 2 ≤ CFSG.Open.pRank 3 S := by
      have := qs_pRank hP hSQ
      rw [hSmap] at this
      omega
    have h1 : normalizer (S : Set G) ≤ Y := h.y1 S hSQ hSrk
    have h2 := normalizer_map_le_map_normalizer (primeComplementCore (G := G) 3) hO
      (hP.to_le hSQ)
    rw [hSmap] at h2
    exact h2.trans (Subgroup.map_mono h1)
  · intro Eb hEbQ hEbA hEb27 Sb hSbEb hSbrk
    obtain ⟨E, hEQ, hEmap⟩ := qs_preimage (T := Q) hEbQ
    have hEA : IsElemAbelian 3 E := qs_elemAbelian hP hEQ (by rw [hEmap]; exact hEbA)
    have hE27 : Nat.card E = 27 := by
      rw [← qs_card_map hP hEQ, hEmap]
      exact hEb27
    obtain ⟨S, hSE, hSmap⟩ := qs_preimage (T := E) (Sb := Sb) (by rw [hEmap]; exact hSbEb)
    have hSQ : S ≤ Q := hSE.trans hEQ
    have hSrk : 1 ≤ CFSG.Open.pRank 3 S := by
      have := qs_pRank hP hSQ
      rw [hSmap] at this
      omega
    have h1 : normalizer (S : Set G) ≤ Y := h.y2 E hEQ hEA hE27 S hSE hSrk
    have h2 := normalizer_map_le_map_normalizer (primeComplementCore (G := G) 3) hO
      (hP.to_le hSQ)
    rw [hSmap] at h2
    exact h2.trans (Subgroup.map_mono h1)

end Cards

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2
