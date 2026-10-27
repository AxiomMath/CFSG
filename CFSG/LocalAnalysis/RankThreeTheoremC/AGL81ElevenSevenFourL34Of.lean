module

public import CFSG.GH74.QTGen4.Leaves.F112.PSU32Model
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81JZeroTwoHolds
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanPRankCommuting
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
import all CFSG.GH74.QTGen4.Leaves.F112.PSU32Model
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding.KFactProofs

@[expose] def KFactSUThreeTwoNoNormalThreePrime : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
    ∀ N : Subgroup ↥(StatedSU 3 2 K), N.Normal → ¬ 3 ∣ Nat.card N → N = ⊥

namespace SevenFourL34

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_oUpperTwo' {X : Subgroup G} {n : G} (hn : n ∈ X) :
    n ∈ Subgroup.normalizer (CFSG.ComponentClassification.AS76b.oUpperTwo X : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, CFSG.ComponentClassification.AS76b.oUpperTwo,
    MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨w, ⟨hwX, hw⟩, rfl⟩
    refine ⟨X.mul_mem (X.mul_mem hn hwX) (X.inv_mem hn), ?_⟩
    have h := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective w
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    change Odd (orderOf (n * w * n⁻¹))
    rwa [h]
  · rintro ⟨hxX, hx⟩
    refine ⟨n⁻¹ * x * n, ⟨by simpa [mul_assoc] using X.mul_mem (X.mul_mem (X.inv_mem hn) hxX) hn,
      ?_⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
    have : orderOf (n⁻¹ * x * n) = orderOf x := by
      have h := orderOf_injective (MulAut.conj n⁻¹).toMonoidHom (MulAut.conj n⁻¹).injective x
      simpa [MulAut.conj_apply] using h
    rwa [this]

theorem oUpperTwo_eq_of_perfect {I : Subgroup G} (h : ⁅I, I⁆ = I) :
    CFSG.ComponentClassification.AS76b.oUpperTwo I = I := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := CFSG.ComponentClassification.AS76b.oUpperTwo I with hT
  have hTI : T ≤ I := oUpperTwo_le_self I
  refine le_antisymm hTI ?_
  haveI : (T.subgroupOf I).Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (fun g hg => mem_normalizer_oUpperTwo' hg)
  have hp : IsPGroup 2 (↥I ⧸ T.subgroupOf I) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨a, ha⟩ := exists_two_pow_mem_oUpperTwo g.2
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha
  haveI : Group.IsNilpotent (↥I ⧸ T.subgroupOf I) := hp.isNilpotent
  have hcomm : commutator ↥I = ⊤ := by
    have h1 : (commutator ↥I).map I.subtype = I := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, h]
    rw [eq_top_iff]
    intro g _
    have : (g : G) ∈ (commutator ↥I).map I.subtype := by rw [h1]; exact g.2
    obtain ⟨c, hc, hcg⟩ := this
    have : c = g := Subtype.ext hcg
    rwa [← this]
  have hcomm' : commutator (↥I ⧸ T.subgroupOf I) = ⊤ := by
    have := congrArg (Subgroup.map (QuotientGroup.mk' (T.subgroupOf I))) hcomm
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, QuotientGroup.range_mk'] at this
    rw [commutator_def]
    exact this
  have hsub : Subsingleton (↥I ⧸ T.subgroupOf I) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact (IsSolvable.commutator_lt_top_of_nontrivial (↥I ⧸ T.subgroupOf I)).ne hcomm'
  intro g hg
  have : (QuotientGroup.mk (⟨g, hg⟩ : ↥I) : ↥I ⧸ T.subgroupOf I) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff] at this
  exact this

theorem eq_one_of_mem_pGroup_two {N : Subgroup G} (hN : IsPGroup 2 N) {g : G} (hg : g ∈ N)
    (h3 : g ^ 3 = 1) : g = 1 := by
  obtain ⟨k, hk⟩ := hN ⟨g, hg⟩
  have hk' : g ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hc : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have := (pow_gcd_eq_one (a := g) (m := 2 ^ k) (n := 3)).mpr ⟨hk', h3⟩
  rwa [Nat.Coprime.gcd_eq_one hc, pow_one] at this

theorem two_le_pRank_of_commuting_mod {Y N C₁ C₂ : Subgroup G} (hN : IsPGroup 2 N)
    (hYN : Y ≤ Subgroup.normalizer (N : Set G))
    {u v : G} (huY : u ∈ Y) (hvY : v ∈ Y) (huC : u ∈ C₁) (hvC : v ∈ C₂)
    (hmeet : (C₁ ⊔ N) ⊓ (C₂ ⊔ N) ≤ N)
    (hu : orderOf u = 3) (hv : orderOf v = 3) (hcomm : u * v * u⁻¹ * v⁻¹ ∈ N) :
    2 ≤ Open.pRank 3 Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hv3 : v ^ 3 = 1 := by rw [← hv]; exact pow_orderOf_eq_one v
  haveI hNn : (N.subgroupOf Y).Normal := ⟨fun n hn g => by
    have := (Subgroup.mem_normalizer_iff.mp (hYN g.2) (n : G)).mp hn
    exact this⟩
  have hNp : ¬ 3 ∣ Nat.card (N.subgroupOf Y) := by
    have hNp2 : IsPGroup 2 ↥(N.subgroupOf Y) := hN.comap_subtype
    obtain ⟨n, hn⟩ := hNp2.exists_card_eq
    rw [hn]
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  have hq := CFSG.SectionRank.pRank_quotient_eq (p := 3) (N.subgroupOf Y) hNp
  have hY : Open.pRank 3 Y = Open.pRank 3 (⊤ : Subgroup ↥Y) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup Y
  rw [hY, ← hq]
  let ub : ↥Y ⧸ N.subgroupOf Y := QuotientGroup.mk ⟨u, huY⟩
  let vb : ↥Y ⧸ N.subgroupOf Y := QuotientGroup.mk ⟨v, hvY⟩
  have hpow : ∀ i : Fin 2, (![ub, vb] i) ^ 3 = 1 := by
    intro i
    fin_cases i
    · show ub ^ 3 = 1
      rw [← QuotientGroup.mk_pow]
      have : (⟨u, huY⟩ : ↥Y) ^ 3 = 1 := Subtype.ext (by simpa using hu3)
      rw [this]; rfl
    · show vb ^ 3 = 1
      rw [← QuotientGroup.mk_pow]
      have : (⟨v, hvY⟩ : ↥Y) ^ 3 = 1 := Subtype.ext (by simpa using hv3)
      rw [this]; rfl
  have hc : Commute ub vb := by
    show ub * vb = vb * ub
    show (QuotientGroup.mk (⟨u, huY⟩ : ↥Y) : ↥Y ⧸ N.subgroupOf Y) *
        QuotientGroup.mk ⟨v, hvY⟩ = QuotientGroup.mk ⟨v, hvY⟩ * QuotientGroup.mk ⟨u, huY⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hYN (Y.inv_mem (Y.mul_mem huY hvY)))
      (u * v * u⁻¹ * v⁻¹)⁻¹).mp (N.inv_mem hcomm)
    have e : ((u * v)⁻¹ * (u * v * u⁻¹ * v⁻¹)⁻¹ * ((u * v)⁻¹)⁻¹ : G) = (u * v)⁻¹ * (v * u) := by
      group
    rw [e] at h1
    simpa using h1
  have hker : ∀ a : Fin 2 → ZMod 3, a ≠ 0 →
      (List.ofFn fun i => (![ub, vb] i) ^ (a i).val).prod ≠ 1 := by
    intro a ha hprod
    have h1 : ub ^ (a 0).val * vb ^ (a 1).val = 1 := by
      simpa [List.ofFn_succ] using hprod
    have h2 : ((⟨u, huY⟩ : ↥Y) ^ (a 0).val * (⟨v, hvY⟩ : ↥Y) ^ (a 1).val) ∈ N.subgroupOf Y := by
      rw [← QuotientGroup.eq_one_iff]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow]
      exact h1
    rw [Subgroup.mem_subgroupOf] at h2
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow] at h2
    have hu' : u ^ (a 0).val ∈ C₁ ⊔ N := Subgroup.mem_sup_left (C₁.pow_mem huC _)
    have hu'' : u ^ (a 0).val ∈ C₂ ⊔ N := by
      have : u ^ (a 0).val = (u ^ (a 0).val * v ^ (a 1).val) * (v ^ (a 1).val)⁻¹ := by group
      rw [this]
      exact (C₂ ⊔ N).mul_mem (Subgroup.mem_sup_right h2)
        ((C₂ ⊔ N).inv_mem (Subgroup.mem_sup_left (C₂.pow_mem hvC _)))
    have hum : u ^ (a 0).val ∈ N := hmeet ⟨hu', hu''⟩
    have hvn : v ^ (a 1).val ∈ N := by
      have : v ^ (a 1).val = (u ^ (a 0).val)⁻¹ * (u ^ (a 0).val * v ^ (a 1).val) := by group
      rw [this]
      exact N.mul_mem (N.inv_mem hum) h2
    have hum1 : u ^ (a 0).val = 1 := eq_one_of_mem_pGroup_two hN hum (by
      rw [← pow_mul, mul_comm, pow_mul, hu3, one_pow])
    have hvn1 : v ^ (a 1).val = 1 := eq_one_of_mem_pGroup_two hN hvn (by
      rw [← pow_mul, mul_comm, pow_mul, hv3, one_pow])
    have d0 : 3 ∣ (a 0).val := by
      have := orderOf_dvd_of_pow_eq_one hum1
      rwa [hu] at this
    have d1 : 3 ∣ (a 1).val := by
      have := orderOf_dvd_of_pow_eq_one hvn1
      rwa [hv] at this
    have z0 : (a 0).val = 0 := Nat.eq_zero_of_dvd_of_lt d0 (ZMod.val_lt (a 0))
    have z1 : (a 1).val = 0 := Nat.eq_zero_of_dvd_of_lt d1 (ZMod.val_lt (a 1))
    apply ha
    funext i
    fin_cases i
    · exact (ZMod.val_eq_zero _).mp z0
    · exact (ZMod.val_eq_zero _).mp z1
  exact CFSG.AGLEmbedding.le_pRank_of_commuting_pow (p := 3) ![ub, vb] hpow
    (fun i j => by
      fin_cases i <;> fin_cases j
      · exact Commute.refl _
      · exact hc
      · exact hc.symm
      · exact Commute.refl _) hker (H := ⊤) (fun i => Subgroup.mem_top _)

theorem three_dvd_of_pow_three {Γ : Type*} [Group Γ] [Finite Γ] {N : Subgroup Γ} {x : Γ}
    (hx : x ∈ N) (h3 : x ^ 3 = 1) (h1 : x ≠ 1) : 3 ∣ Nat.card N := by
  have ho : orderOf x = 3 := orderOf_eq_prime h3 h1
  rw [← ho]
  exact Subgroup.orderOf_dvd_natCard N hx

theorem perm_three_aux : ∀ g : Equiv.Perm (Fin 3), g ≠ 1 → g ^ 3 = 1 ∨
    ∃ c : Equiv.Perm (Fin 3), (c * g * c⁻¹ * g⁻¹) ^ 3 = 1 ∧ c * g * c⁻¹ * g⁻¹ ≠ 1 := by
  decide +kernel

theorem perm_three_normal_eq_bot (N : Subgroup (Equiv.Perm (Fin 3))) [hN : N.Normal]
    (h : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  by_contra hne
  obtain ⟨⟨g, hg'⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hg2 : g ≠ 1 := fun h' => hg1 (Subtype.ext h')
  rcases perm_three_aux g hg2 with h3 | ⟨c, h3, h1⟩
  · exact h (three_dvd_of_pow_three hg' h3 hg2)
  · have hx : c * g * c⁻¹ * g⁻¹ ∈ N :=
      N.mul_mem (hN.conj_mem g hg' c) (N.inv_mem hg')
    exact h (three_dvd_of_pow_three hx h3 h1)

theorem normal_eq_bot_of_not_three_dvd (hSU : KFactSUThreeTwoNoNormalThreePrime) {T : Type}
    [Group T] [Finite T] (hT : IsSymThreeOrSUThreeTwo T) (N : Subgroup T) [hN : N.Normal]
    (h : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  rcases hT with ⟨⟨e⟩⟩ | ⟨K, hK, hKf, hcard, ⟨e⟩⟩
  · haveI : (N.map e.toMonoidHom).Normal := hN.map _ e.surjective
    have hc : Nat.card (N.map e.toMonoidHom) = Nat.card N :=
      Subgroup.card_map_of_injective e.injective
    have := perm_three_normal_eq_bot (N.map e.toMonoidHom) (by rwa [hc])
    exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).mp this
  · haveI : (N.map e.toMonoidHom).Normal := hN.map _ e.surjective
    have hc : Nat.card (N.map e.toMonoidHom) = Nat.card N :=
      Subgroup.card_map_of_injective e.injective
    have := hSU K hcard (N.map e.toMonoidHom) inferInstance (by rwa [hc])
    exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).mp this

open CFSG.ComponentClassification

def kPre (p : ℕ) (H : Subgroup G) (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
    Subgroup G :=
  (K.comap (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype

theorem d1LiftX_le_kPre (p : ℕ) (H R : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : d1LiftX p H R K ≤ kPre p H K :=
  Subgroup.map_mono inf_le_right

theorem le_normalizer_kPre {p : ℕ} {H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hK : K.Normal) :
    H ≤ Subgroup.normalizer (kPre p H K : Set G) := by
  haveI := hK
  have hN : (K.comap (QuotientGroup.mk' (primeComplementCore (G := H) p))).Normal :=
    Subgroup.Normal.comap inferInstance _
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
  change ((kPre p H K).subgroupOf H).Normal
  have e : (kPre p H K).subgroupOf H =
      K.comap (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [e]
  exact hN

theorem kPre_inf_d1PlusCore_le {p : ℕ} {H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hZ : Subgroup.center K = ⊥) :
    kPre p H K ⊓ d1PlusCore p H K ≤ (primeComplementCore (G := H) p).map H.subtype := by
  rintro n ⟨⟨h, hhK, rfl⟩, ⟨h', hh'C, hh'⟩⟩
  have hh : h' = h := Subtype.ext hh'
  subst hh
  have hc : (⟨QuotientGroup.mk' (primeComplementCore (G := H) p) h', hhK⟩ : K) ∈
      Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hh'C) k k.2)
  rw [hZ, Subgroup.mem_bot] at hc
  have h1 : QuotientGroup.mk' (primeComplementCore (G := H) p) h' = 1 := congrArg Subtype.val hc
  exact ⟨h', (QuotientGroup.eq_one_iff h').mp h1, rfl⟩

theorem false_of_orderOf_three {H : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hZ : Subgroup.center K = ⊥) {I₀ : Subgroup G}
    (hOX : AS76b.oUpperTwo I₀ ≤ d1PlusCore 3 H K) {n : G} (hn : n ∈ I₀) (hnK : n ∈ kPre 3 H K)
    (hno : orderOf n = 3) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnO : n ∈ AS76b.oUpperTwo I₀ := Subgroup.subset_closure ⟨hn, by rw [hno]; decide⟩
  obtain ⟨c, hc, rfl⟩ := kPre_inf_d1PlusCore_le hZ ⟨hnK, hOX hnO⟩
  have ho : orderOf c = 3 := ((Subgroup.orderOf_coe c).symm).trans hno
  have h1 : 3 ∣ Nat.card (primeComplementCore (G := H) 3) := by
    have := Subgroup.orderOf_dvd_natCard (primeComplementCore (G := H) 3) hc
    rwa [ho] at this
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (primeComplementCore_coprime (G := H) 3) h1

theorem commutator_mem_pCoreOf {H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hKn : K.Normal)
    (hZ : Subgroup.center K = ⊥) (hSU : KFactSUThreeTwoNoNormalThreePrime)
    {I₀ A : Subgroup G} (hI₀H : I₀ ≤ H) (hAK : A ≤ kPre 3 H K)
    (hAN : A ≤ Subgroup.normalizer (I₀ : Set G)) (hOX : AS76b.oUpperTwo I₀ ≤ d1PlusCore 3 H K)
    (hsh : IsSymThreeOrSUThreeTwo (↥I₀ ⧸ CFSG.pCore 2 ↥I₀)) :
    ∀ b ∈ A, ∀ x ∈ I₀, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 I₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S : Set G := {y | ∃ b ∈ A, ∃ x ∈ I₀, y = b * x * b⁻¹ * x⁻¹} with hS
  set N : Subgroup G := Subgroup.closure S with hN
  have hSI : S ⊆ I₀ := by
    rintro _ ⟨b, hb, x, hx, rfl⟩
    have h1 : b * x * b⁻¹ ∈ I₀ := (Subgroup.mem_normalizer_iff.mp (hAN hb) x).mp hx
    exact I₀.mul_mem h1 (I₀.inv_mem hx)
  have hSK : S ⊆ kPre 3 H K := by
    rintro _ ⟨b, hb, x, hx, rfl⟩
    have h1 : x * b⁻¹ * x⁻¹ ∈ kPre 3 H K :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_kPre hKn (hI₀H hx)) b⁻¹).mp
        ((kPre 3 H K).inv_mem (hAK hb))
    have := (kPre 3 H K).mul_mem (hAK hb) h1
    simpa [mul_assoc] using this
  have hNI : N ≤ I₀ := (Subgroup.closure_le _).mpr hSI
  have hNK : N ≤ kPre 3 H K := (Subgroup.closure_le _).mpr hSK
  have hconj : ∀ y ∈ I₀, ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
    intro y hy
    have hle : N ≤ N.comap (MulAut.conj y).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨b, hb, x, hx, rfl⟩
      show y * (b * x * b⁻¹ * x⁻¹) * y⁻¹ ∈ N
      have e : y * (b * x * b⁻¹ * x⁻¹) * y⁻¹ =
          (b * y * b⁻¹ * y⁻¹)⁻¹ * (b * (y * x) * b⁻¹ * (y * x)⁻¹) := by group
      rw [e]
      exact N.mul_mem (N.inv_mem (Subgroup.subset_closure ⟨b, hb, y, hy, rfl⟩))
        (Subgroup.subset_closure ⟨b, hb, y * x, I₀.mul_mem hy hx, rfl⟩)
    intro n hn
    exact hle hn
  have hN3 : ¬ 3 ∣ Nat.card N := by
    intro h3
    obtain ⟨⟨n, hn⟩, hno⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 3 h3
    rw [Subgroup.orderOf_mk] at hno
    exact false_of_orderOf_three hZ hOX (hNI hn) (hNK hn) hno
  have hNI' : N.subgroupOf I₀ ≤ ⊤ := le_top
  haveI hNn : (N.subgroupOf I₀).Normal := ⟨fun n hn g => hconj g.1 g.2 n hn⟩
  haveI hNb : ((N.subgroupOf I₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I₀))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  have hcard : Nat.card (N.subgroupOf I₀) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNI).toEquiv
  have hbot : (N.subgroupOf I₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I₀)) = ⊥ :=
    normal_eq_bot_of_not_three_dvd hSU hsh _ (fun h => hN3 (by
      rw [← hcard]
      exact h.trans (Subgroup.card_map_dvd _ _)))
  have hNp : N ≤ pCoreOf 2 I₀ := by
    intro n hn
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥I₀) (⟨n, hNI hn⟩ : ↥I₀) ∈
        (N.subgroupOf I₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I₀)) :=
      Subgroup.mem_map_of_mem _ hn
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨n, hNI hn⟩, h1, rfl⟩
  intro b hb x hx
  exact hNp (Subgroup.subset_closure ⟨b, hb, x, hx, rfl⟩)

section SUNoNormal

open CFSG.GH74.QTGen4.Leaves.F112 KFactProofs.SUThreeTwoShape

variable {K : Type} [Field K]

theorem eq_zero_of_mul_eq {x a b : K} (hne : a ≠ b) (h : x * a = b * x) : x = 0 := by
  have : x * (a - b) = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)

theorem scalar_of_comm {ω : K} (hω : ω ^ 2 = ω + 1) (M : Matrix (Fin 3) (Fin 3) K)
    (hS : M * mS = mS * M) (hD : M * mD ω = mD ω * M) :
    M = Matrix.scalar (Fin 3) (M 0 0) := by
  have n10 : (1 : K) ≠ ω := by
    intro h
    rw [← h] at hω
    have : (1 : K) = 0 := by linear_combination -hω
    exact one_ne_zero this
  have n20 : (1 : K) ≠ ω ^ 2 := by
    intro h
    have hw : ω = 0 := by linear_combination -h - hω
    rw [hw] at h
    norm_num at h
  have n21 : ω ≠ ω ^ 2 := by
    intro h
    have : (1 : K) = 0 := by linear_combination -hω - h
    exact one_ne_zero this
  have hmD : mD ω = Matrix.diagonal ![1, ω, ω ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mD]
  rw [hmD] at hD
  have hoff : ∀ i j : Fin 3, i ≠ j → M i j = 0 := by
    intro i j hij
    have e := congrFun (congrFun hD i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    fin_cases i <;> fin_cases j <;> simp at e hij ⊢
    · exact eq_zero_of_mul_eq n10.symm (by linear_combination e)
    · exact eq_zero_of_mul_eq n20.symm (by linear_combination e)
    · exact eq_zero_of_mul_eq n10 (by linear_combination e)
    · exact eq_zero_of_mul_eq n21.symm (by linear_combination e)
    · exact eq_zero_of_mul_eq n20 (by linear_combination e)
    · exact eq_zero_of_mul_eq n21 (by linear_combination e)
  have e0 := congrFun (congrFun hS 0) 2
  have e1 := congrFun (congrFun hS 1) 0
  simp [mS, Matrix.mul_apply, Fin.sum_univ_three] at e0 e1
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp [Matrix.scalar_apply] <;> grind
  · rw [hoff i j hij]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij]

theorem kFactSUThreeTwoNoNormalThreePrime_holds : KFactSUThreeTwoNoNormalThreePrime := by
  intro K _ _ hK N hN h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω, h2⟩ := exists_omega hK
  let o : OmegaData K := ⟨ω, hω, h2⟩
  have hrel : Heis3Rel (OmegaData.sS o) (OmegaData.sD o) (sZ o) :=
    ⟨sZ_central o, sZ_cube o, OmegaData.sS_cube o, OmegaData.sD_cube o, sS_mul_sD o⟩
  have hcard := card_SUg hK
  have hord : orderOf (OmegaData.sF o) = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := OmegaData.sF o)
      (by simpa using sF_sq_ne_one o) (by simpa using sF_four o)
    simpa using this
  haveI hEn : (heisSubgroup hrel).Normal := heisSubgroup_normal hcard hrel (sZ_ne_one o)
    (hrel.F_mem_normalizer (sF_mul_sS o) (sF_mul_sD o)) hord
  have hE27 : Nat.card (heisSubgroup hrel) = 27 := card_heisSubgroup hcard hrel (sZ_ne_one o)
  have hdisj : Disjoint N (heisSubgroup hrel) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hE27, show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact Nat.Coprime.pow_right 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
  have hcomm : ∀ n ∈ N, ∀ s ∈ heisSubgroup hrel, n * s = s * n := by
    intro n hn s hs
    have h1 : n * s * n⁻¹ * s⁻¹ ∈ N := by
      have e : n * (s * n⁻¹ * s⁻¹) = n * s * n⁻¹ * s⁻¹ := by group
      rw [← e]
      exact N.mul_mem hn (hN.conj_mem n⁻¹ (N.inv_mem hn) s)
    have h2 : n * s * n⁻¹ * s⁻¹ ∈ heisSubgroup hrel :=
      (heisSubgroup hrel).mul_mem (hEn.conj_mem s hs n) ((heisSubgroup hrel).inv_mem hs)
    have h' : n * s * n⁻¹ * s⁻¹ = 1 := Subgroup.disjoint_def.mp hdisj h1 h2
    calc n * s = (n * s * n⁻¹ * s⁻¹) * (s * n) := by group
      _ = s * n := by rw [h', one_mul]
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  by_contra hn1
  have hS := congrArg mat (hcomm n hn _ hrel.S_mem)
  have hD := congrArg mat (hcomm n hn _ hrel.D_mem)
  simp only [mat_mul, OmegaData.sS, OmegaData.sD, mat_suMk] at hS hD
  obtain ⟨a, hsc⟩ : ∃ a, mat n = Matrix.scalar (Fin 3) a := ⟨_, scalar_of_comm hω (mat n) hS hD⟩
  have hdet : (mat n).det = 1 := CFSG.Open.StatedAPI.det_of_mem_statedSU n.2
  rw [hsc] at hdet
  have ha : a ^ 3 = 1 := by
    simpa [Matrix.scalar_apply, Matrix.det_diagonal] using hdet
  have hn3 : n ^ 3 = 1 := by
    apply su_ext
    rw [mat_pow, mat_one, hsc, ← map_pow, ha, map_one]
  exact h3 (three_dvd_of_pow_three hn hn3 hn1)

end SUNoNormal

end SevenFourL34

variable {G : Type} [Group G] [Finite G]

variable (G) in
@[expose] def AGL81NineThreeNormalCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → K.Normal

end CFSG.LocalAnalysis.RankThreeTheoremC
