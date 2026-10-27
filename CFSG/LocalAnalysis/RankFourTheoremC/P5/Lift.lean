module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointCover
import CFSG.LocalAnalysis.PreuniquenessRankFour.RankTwo
import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

open CFSG.ABGLocalTools CFSG.Open Subgroup

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

variable {G : Type} [Group G] [Finite G]

theorem not_two_dvd_card_of_pow_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q : Type*} [Group Q]
    [Finite Q] (h : ∀ g : Q, g ^ p = 1) : ¬ 2 ∣ Nat.card Q := by
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 hdvd
  have hd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (h g)
  rw [hg] at hd
  have h2p : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp hd
  exact hp2 h2p.symm

theorem not_two_dvd_relIndex_inf_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K O : Subgroup G}
    (hKO : K ≤ normalizer (O : Set G)) (h : ∀ k ∈ K, k ^ p ∈ O) :
    ¬ 2 ∣ (K ⊓ O).relIndex K := by
  have hn : ((K ⊓ O).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (le_normalizer_inf' Subgroup.le_normalizer hKO)
  refine not_two_dvd_card_of_pow_p hp2 (Q := ↥K ⧸ (K ⊓ O).subgroupOf K) fun g => ?_
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr ⟨K.pow_mem k.2 p, h k k.2⟩

theorem exists_elemAbelian_normalizing_involClosure_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {O R Y A : Subgroup G} {x : G}
    (hOR : O ≤ R) (hRO : R ≤ normalizer (O : Set G))
    (hYR : Y ≤ normalizer (R : Set G)) (hYO : Y ≤ normalizer (O : Set G))
    (hOp : ¬ p ∣ Nat.card O) (hRp : ∀ r ∈ R, r ^ p ∈ O)
    (hRab : ∀ r ∈ R, ∀ r' ∈ R, r * r' * r⁻¹ * r'⁻¹ ∈ O)
    (hY2 : IsPGroup 2 Y) (hYO' : IsSylowOf 2 (Y ⊓ O) O)
    (hxp : x ^ p = 1) (hxR : x ∉ R) (hxRn : x ∈ normalizer (R : Set G))
    (hxc : ∀ r ∈ R, x * r * x⁻¹ * r⁻¹ ∈ O) (hxY : x ∈ normalizer (Y : Set G))
    (hAR : A ≤ R) (hAO : A ⊓ O = ⊥) (hA : p ^ 2 ≤ Nat.card A)
    (hAfix : ∀ a ∈ A, ∀ i ∈ Y, i ^ 2 = 1 → a * i * a⁻¹ * i⁻¹ ∈ O) :
    ∃ E : Subgroup G, E ≤ normalizer (involClosure Y : Set G) ∧ E ≤ R ⊔ zpowers x ∧
      IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpr : p.Prime := Fact.out
  set S : Subgroup G := Y ⊓ O with hS
  set N : Subgroup G := R ⊓ normalizer (S : Set G) with hN
  have hSO : S ≤ O := inf_le_right
  have hSY : S ≤ Y := inf_le_left
  have hSN : S ≤ N := le_inf (hSO.trans hOR) Subgroup.le_normalizer
  have hNS : N ≤ normalizer (S : Set G) := inf_le_right
  have hNR : N ≤ R := inf_le_left
  have hYS : Y ≤ normalizer (S : Set G) := le_normalizer_inf' Subgroup.le_normalizer hYO
  have hYN : Y ≤ normalizer (N : Set G) :=
    le_normalizer_inf' hYR (hYS.trans Subgroup.le_normalizer)
  have hodd : ¬ 2 ∣ S.relIndex N := by
    have hSNO : S ≤ N ⊓ O := le_inf hSN hSO
    have h1 : IsSylowOf 2 S (N ⊓ O) := hYO'.of_le hSNO inf_le_right
    have h2 : ¬ 2 ∣ S.relIndex (N ⊓ O) := (isSylowOf_iff.mp h1).2.2
    have h3 : ¬ 2 ∣ (N ⊓ O).relIndex N :=
      not_two_dvd_relIndex_inf_p hp2 (hNR.trans hRO) fun n hn => hRp n (hNR hn)
    rw [← Subgroup.relIndex_mul_relIndex S (N ⊓ O) N hSNO inf_le_left]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
    · exact h2 h
    · exact h3 h
  obtain ⟨T, hST, hTN, hYT, hTidx, hT3⟩ := exists_normalized_sylow_mod (p := 2) (q := p)
    hSN hNS hYS hYN hY2 hodd
  have hTO : T ⊓ O = S := by
    refine le_antisymm ?_ (le_inf hST hSO)
    rintro t ⟨htT, htO⟩
    obtain ⟨k, hk⟩ := hT3 t htT
    have hd : orderOf t ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨t, htO⟩ : O)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (p ^ k) (orderOf t) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hpr).mpr
        (fun h => hOp (h.trans hd)))
    obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
    have htc : t = (t ^ (p ^ k)) ^ c := hc.symm
    rw [htc]
    exact S.pow_mem hk c
  have hO'n : (O.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOR).mpr hRO
  have hRTO : ∀ r ∈ R, ∃ t ∈ T, ∃ o ∈ O, r = t * o := by
    set φ : N →* R ⧸ O.subgroupOf R :=
      (QuotientGroup.mk' (O.subgroupOf R)).comp (Subgroup.inclusion hNR) with hφ
    have hfrat : ∀ r ∈ R, ∃ n ∈ N, ∃ o ∈ O, r = n * o := by
      intro r hr
      obtain ⟨o, ho, m, hm, hrm⟩ := exists_mul_normalizer_of_isSylowOf hYO' hRO hr
      have hmR : m ∈ R := by
        have : m = o⁻¹ * r := by rw [hrm]; group
        rw [this]
        exact R.mul_mem (R.inv_mem (hOR ho)) hr
      refine ⟨m, ⟨hmR, hm⟩, m⁻¹ * o * m, ?_, by rw [hrm]; group⟩
      have := (mem_normalizer_iff.mp (hRO (R.inv_mem hmR)) o).mp ho
      simpa [mul_assoc] using this
    have hφsurj : Function.Surjective φ := by
      intro g
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨n, hn, o, ho, hrn⟩ := hfrat r r.2
      refine ⟨⟨n, hn⟩, ?_⟩
      show (QuotientGroup.mk (⟨n, hNR hn⟩ : R) : R ⧸ O.subgroupOf R) = QuotientGroup.mk r
      rw [QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      have : ((⟨n, hNR hn⟩ : R)⁻¹ * r : R) = ⟨o, hOR ho⟩ := Subtype.ext (by
        change n⁻¹ * (r : G) = o
        rw [hrn]; group)
      rw [this]
      exact ho
    have hRbar3 : IsPGroup p (R ⧸ O.subgroupOf R) := fun g => ⟨1, by
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective g
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (hRp r r.2)⟩
    obtain ⟨a, ha⟩ := hRbar3.exists_card_eq
    set Tim : Subgroup (R ⧸ O.subgroupOf R) := (T.subgroupOf N).map φ with hTim
    have hTimidx : Tim.index ∣ T.relIndex N := Subgroup.index_map_dvd (T.subgroupOf N) hφsurj
    have hTim1 : Tim.index = 1 := by
      have hdvd : Tim.index ∣ p ^ a := ha ▸ Subgroup.index_dvd_card Tim
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hpr).mp hdvd
      rcases Nat.eq_zero_or_pos b with rfl | hb0
      · simpa using hb
      · exfalso
        apply hTidx
        exact (dvd_pow_self p hb0.ne').trans (hb ▸ hTimidx)
    have htop : Tim = ⊤ := Subgroup.index_eq_one.mp hTim1
    intro r hr
    obtain ⟨n, hn, o, ho, hrn⟩ := hfrat r hr
    have hφn : φ ⟨n, hn⟩ ∈ Tim := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨t', ht', hφt⟩ := hφn
    have ht : (t' : G) ∈ T := ht'
    have hto : (t' : G)⁻¹ * n ∈ O := by
      have := (QuotientGroup.eq (a := (⟨t', hNR t'.2⟩ : R)) (b := ⟨n, hNR hn⟩)).mp hφt
      have h2 := Subgroup.mem_subgroupOf.mp this
      simpa using h2
    refine ⟨t', ht, (t' : G)⁻¹ * n * o, O.mul_mem hto ho, ?_⟩
    rw [hrn]; group
  have hTR : T ≤ R := hTN.trans hNR
  have hTnorm : ∀ t ∈ T, (∀ i ∈ Y, i ^ 2 = 1 → t * i * t⁻¹ * i⁻¹ ∈ O) →
      t ∈ normalizer (involClosure Y : Set G) := by
    intro t htT hcomm
    refine mem_normalizer_involClosure_of_forall fun i hiY hi2 => ?_
    have h1 : t * i * t⁻¹ * i⁻¹ ∈ T := by
      have : i * t⁻¹ * i⁻¹ ∈ T := (mem_normalizer_iff.mp (hYT hiY) t⁻¹).mp (T.inv_mem htT)
      simpa only [mul_assoc] using T.mul_mem htT this
    have h2 : t * i * t⁻¹ * i⁻¹ ∈ S := by
      rw [← hTO]
      exact ⟨h1, hcomm i hiY hi2⟩
    have h3 : t * i * t⁻¹ = (t * i * t⁻¹ * i⁻¹) * i := by group
    rw [h3]
    exact Y.mul_mem (hSY h2) hiY
  set Y₁ : Subgroup G := involClosure Y with hY₁
  set D : Subgroup G := R ⊓ normalizer (Y₁ : Set G) with hD
  have hDR : D ≤ R := inf_le_left
  have hAD : ∀ a ∈ A, ∃ d ∈ D, ∃ o ∈ O, a = d * o := by
    intro a ha
    obtain ⟨t, htT, o, hoO, hat⟩ := hRTO a (hAR ha)
    have hcomm : ∀ i ∈ Y, i ^ 2 = 1 → t * i * t⁻¹ * i⁻¹ ∈ O := by
      intro i hi hi2
      have h1 := hAfix a ha i hi hi2
      have ho₂ : (i⁻¹ * o⁻¹ * i) * o ∈ O := by
        have := (mem_normalizer_iff.mp (hYO (Y.inv_mem hi)) o⁻¹).mp (O.inv_mem hoO)
        simp only [inv_inv] at this
        exact O.mul_mem this hoO
      have h2 : a * ((i⁻¹ * o⁻¹ * i) * o) * a⁻¹ ∈ O :=
        (mem_normalizer_iff.mp (hRO (hAR ha)) _).mp ho₂
      have h3 : i * (a * ((i⁻¹ * o⁻¹ * i) * o) * a⁻¹) * i⁻¹ ∈ O :=
        (mem_normalizer_iff.mp (hYO hi) _).mp h2
      have h4 : t * i * t⁻¹ * i⁻¹ = (a * i * a⁻¹ * i⁻¹) *
          (i * (a * ((i⁻¹ * o⁻¹ * i) * o) * a⁻¹) * i⁻¹) := by
        subst hat
        group
      rw [h4]
      exact O.mul_mem h1 h3
    exact ⟨t, ⟨hTR htT, hTnorm t htT hcomm⟩, o, hoO, hat⟩
  have hD9 : p ^ 2 ∣ Nat.card D := by
    set ψA : A →* R ⧸ O.subgroupOf R :=
      (QuotientGroup.mk' (O.subgroupOf R)).comp (Subgroup.inclusion hAR) with hψA
    have hψinj : Function.Injective ψA := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have h1 : (⟨a, hAR a.2⟩ : R) ∈ O.subgroupOf R := (QuotientGroup.eq_one_iff _).mp ha
      have h2 : (a : G) ∈ A ⊓ O := ⟨a.2, h1⟩
      rw [hAO, Subgroup.mem_bot] at h2
      exact Subtype.ext h2
    set φD : D →* R ⧸ O.subgroupOf R :=
      (QuotientGroup.mk' (O.subgroupOf R)).comp (Subgroup.inclusion hDR) with hφD
    have hrange : ψA.range ≤ φD.range := by
      rintro _ ⟨a, rfl⟩
      obtain ⟨d, hd, o, ho, hado⟩ := hAD a a.2
      refine ⟨⟨d, hd⟩, ?_⟩
      show (QuotientGroup.mk (⟨d, hDR hd⟩ : R) : R ⧸ O.subgroupOf R) = QuotientGroup.mk ⟨a, hAR a.2⟩
      rw [QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      change d⁻¹ * (a : G) ∈ O
      rw [hado]
      simpa using ho
    have hRbar3 : IsPGroup p (R ⧸ O.subgroupOf R) := fun g => ⟨1, by
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective g
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (hRp r r.2)⟩
    obtain ⟨a, ha⟩ := hRbar3.exists_card_eq
    have hcardA : Nat.card A = Nat.card ψA.range :=
      Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv
    have hge : p ^ 2 ≤ Nat.card φD.range :=
      hA.trans (hcardA ▸ Subgroup.card_le_of_le hrange)
    have hdvd : Nat.card φD.range ∣ p ^ a := ha ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hpr).mp hdvd
    have hb2 : 2 ≤ b := by
      by_contra hlt
      have hb1 : b ≤ 1 := by omega
      have hpb : Nat.card φD.range ≤ p ^ 1 := by
        rw [hb]; exact Nat.pow_le_pow_right hpr.pos hb1
      have hlt2 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hpr.one_lt (by norm_num)
      exact absurd (hge.trans hpb) (not_le.mpr hlt2)
    have h9 : p ^ 2 ∣ Nat.card φD.range := by
      rw [hb]
      exact pow_dvd_pow p hb2
    exact h9.trans (Subgroup.card_range_dvd φD)
  have hxY₁ : x ∈ normalizer (Y₁ : Set G) := mem_normalizer_involClosure hxY
  have hxD : x ∈ normalizer (D : Set G) :=
    le_normalizer_inf' (A := zpowers x) (zpowers_le.mpr hxRn)
      (zpowers_le.mpr (Subgroup.le_normalizer hxY₁)) (mem_zpowers x)
  set Dp : Subgroup G := D ⊔ zpowers x with hDp
  have hDDp : D ≤ Dp := le_sup_left
  have hxDp : zpowers x ≤ Dp := le_sup_right
  have hDpD : Dp ≤ normalizer (D : Set G) := sup_le Subgroup.le_normalizer (zpowers_le.mpr hxD)
  have hxPg : IsPGroup p ((zpowers x).subgroupOf Dp) := by
    have : IsPGroup p (zpowers x) := by
      have hxo : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
      rcases (Nat.dvd_prime hpr).mp hxo with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
    exact this.comap_subtype
  obtain ⟨Q3, hQ3⟩ := hxPg.exists_le_sylow
  set P3 : Subgroup G := (Q3 : Subgroup Dp).map Dp.subtype with hP3
  have hP3s : IsSylowOf p P3 Dp := ⟨Q3, rfl⟩
  have hxP3 : x ∈ P3 := by
    have : (⟨x, hxDp (mem_zpowers x)⟩ : Dp) ∈ (Q3 : Subgroup Dp) :=
      hQ3 (Subgroup.mem_subgroupOf.mpr (mem_zpowers x))
    exact ⟨_, this, rfl⟩
  set D₃ : Subgroup G := P3 ⊓ D with hD₃
  have hD₃s : IsSylowOf p D₃ D := hP3s.inf_of_le_normalizer hDDp hDpD
  have hD₃D : D₃ ≤ D := inf_le_right
  have hD₃p : IsPGroup p D₃ := hD₃s.isPGroup
  have hD₃O : D₃ ⊓ O = ⊥ := by
    obtain ⟨n, hn⟩ := hD₃p.exists_card_eq
    exact (Subgroup.disjoint_of_coprime_natCard (by
      rw [hn]
      exact Nat.Coprime.pow_left n
        ((Nat.Prime.coprime_iff_not_dvd hpr).mpr hOp))).eq_bot
  have hD₃9 : p ^ 2 ≤ Nat.card D₃ := by
    rw [hD₃s.card_eq]
    have hpos : Nat.card D ≠ 0 := Nat.card_pos.ne'
    have h2 : 2 ≤ (Nat.card D).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hpr hpos).mp hD9
    exact Nat.pow_le_pow_right hpr.pos h2
  have hxD₃ : ∀ d ∈ D₃, x * d = d * x := by
    intro d hd
    have h1 : x * d * x⁻¹ ∈ D₃ := ⟨P3.mul_mem (P3.mul_mem hxP3 hd.1) (P3.inv_mem hxP3),
      (mem_normalizer_iff.mp hxD d).mp (hD₃D hd)⟩
    have h2 : x * d * x⁻¹ * d⁻¹ ∈ D₃ := D₃.mul_mem h1 (D₃.inv_mem hd)
    have h3 : x * d * x⁻¹ * d⁻¹ ∈ O := hxc d (hDR (hD₃D hd))
    have h4 : x * d * x⁻¹ * d⁻¹ ∈ D₃ ⊓ O := ⟨h2, h3⟩
    rw [hD₃O, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
    exact h4
  have hxnD₃ : x ∉ D₃ := fun h => hxR (hDR (hD₃D h))
  have hD₃el : IsElemAbelian p D₃ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun d hd => ?_⟩
    · have h1 : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ D₃ ⊓ O :=
        ⟨D₃.mul_mem (D₃.mul_mem (D₃.mul_mem a.2 b.2) (D₃.inv_mem a.2)) (D₃.inv_mem b.2),
          hRab a (hDR (hD₃D a.2)) b (hDR (hD₃D b.2))⟩
      rw [hD₃O, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact Subtype.ext h1
    · have h1 : d ^ p ∈ D₃ ⊓ O := ⟨D₃.pow_mem hd p, hRp d (hDR (hD₃D hd))⟩
      rw [hD₃O, Subgroup.mem_bot] at h1
      exact h1
  have hcommE : D₃ ≤ centralizer ((zpowers x : Subgroup G) : Set G) := by
    intro d hd
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute x d from hxD₃ d hd) k).eq
  refine ⟨D₃ ⊔ zpowers x, sup_le (hD₃D.trans inf_le_right) (zpowers_le.mpr hxY₁),
    sup_le_sup_right (hD₃D.trans hDR) _,
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p hD₃el
      (isElemAbelian_zpowers' hxp) hcommE, ?_⟩
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hpr D₃ hxp hxnD₃
    (fun e he => (hxD₃ e he).symm)]
  calc p ^ 3 = p ^ 2 * p := by ring
    _ ≤ Nat.card D₃ * p := Nat.mul_le_mul hD₃9 le_rfl

end CFSG.LocalAnalysis.RankFourTheoremC.P5
