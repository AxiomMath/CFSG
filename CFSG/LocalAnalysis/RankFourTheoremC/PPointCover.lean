module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.PreuniquenessRankFour.RankTwo
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.LocalVocabulary

public section

open CFSG.ABGLocalTools CFSG.Open Subgroup

namespace CFSG.LocalAnalysis.RankFourTheoremC

variable {G : Type} [Group G] [Finite G]

theorem exists_sylowOf_normalized_of_coprime {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {O B : Subgroup G} (hBp : IsPGroup p B) (hBO : B ≤ normalizer (O : Set G))
    (hOp : ¬ p ∣ Nat.card O) :
    ∃ T : Subgroup G, IsSylowOf q T O ∧ B ≤ normalizer (T : Set G) := by
  classical
  let φ : ↥B →* MulAut ↥O := O.normalizerMonoidHom.comp (Subgroup.inclusion hBO)
  let _ : MulDistribMulAction ↥B ↥O := MulDistribMulAction.compHom ↥O φ
  let _ : MulAction ↥B (Sylow q ↥O) := Sylow.pointwiseMulAction
  have hcard : ¬ p ∣ Nat.card (Sylow q ↥O) := by
    intro h
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow q ↥O))
    exact hOp (h.trans (Q.card_dvd_index.trans (Subgroup.index_dvd_card _)))
  obtain ⟨Q₀, hQ₀⟩ := hBp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q ↥O) hcard
  refine ⟨(Q₀ : Subgroup ↥O).map O.subtype, ⟨Q₀, rfl⟩, ?_⟩
  rw [Subgroup.le_normalizer_iff]
  rintro b hb _ ⟨y, hy, rfl⟩
  have hfix : (⟨b, hb⟩ : ↥B) • Q₀ = Q₀ := (MulAction.mem_fixedPoints.mp hQ₀) ⟨b, hb⟩
  have hmem : (⟨b, hb⟩ : ↥B) • y ∈ (Q₀ : Subgroup ↥O) := by
    have h := Subgroup.smul_mem_pointwise_smul y (⟨b, hb⟩ : ↥B) (Q₀ : Subgroup ↥O) hy
    rwa [← Sylow.pointwise_smul_def, hfix] at h
  refine ⟨_, hmem, ?_⟩
  change (((O.normalizerMonoidHom) (Subgroup.inclusion hBO ⟨b, hb⟩)) y : G) = _
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rfl


theorem exists_normalized_sylow_mod {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {N S B : Subgroup G} (hSN : S ≤ N) (hNS : N ≤ normalizer (S : Set G))
    (hBS : B ≤ normalizer (S : Set G)) (hBN : B ≤ normalizer (N : Set G))
    (hBp : IsPGroup p B) (hodd : ¬ p ∣ S.relIndex N) :
    ∃ T : Subgroup G, S ≤ T ∧ T ≤ N ∧ B ≤ normalizer (T : Set G) ∧ ¬ q ∣ T.relIndex N ∧
      ∀ t ∈ T, ∃ k : ℕ, t ^ (q ^ k) ∈ S := by
  set X : Subgroup G := N ⊔ B with hX
  have hNX : N ≤ X := le_sup_left
  have hBX : B ≤ X := le_sup_right
  have hXS : X ≤ normalizer (S : Set G) := sup_le hNS hBS
  have hXN : X ≤ normalizer (N : Set G) := sup_le Subgroup.le_normalizer hBN
  have hSX : S ≤ X := hSN.trans hNX
  set S' : Subgroup X := S.subgroupOf X with hS'
  set N' : Subgroup X := N.subgroupOf X with hN'
  set B' : Subgroup X := B.subgroupOf X with hB'
  have hS'norm : S'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSX).mpr hXS
  have hN'norm : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hXN
  have hS'N' : S' ≤ N' := fun s hs => hSN hs
  set π : X →* X ⧸ S' := QuotientGroup.mk' S' with hπ
  have hπker : π.ker = S' := QuotientGroup.ker_mk' S'
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective S'
  set Nh : Subgroup (X ⧸ S') := N'.map π with hNh
  set Bh : Subgroup (X ⧸ S') := B'.map π with hBh
  have hBhp : IsPGroup p Bh := (hBp.comap_subtype : IsPGroup p B').map π
  have hBhN : Bh ≤ normalizer (Nh : Set (X ⧸ S')) := by
    have h1 : B' ≤ normalizer (N' : Set X) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map π)
  have hNhcard : Nat.card Nh = S.relIndex N := by
    have h1 := Subgroup.relIndex_map_map π (⊥ : Subgroup X) N'
    rw [Subgroup.map_bot, hπker, bot_sup_eq, sup_eq_left.mpr hS'N'] at h1
    rw [Subgroup.relIndex_bot_left] at h1
    rw [hNh, h1, hS', hN', Subgroup.relIndex_subgroupOf hNX]
  have hNhp : ¬ p ∣ Nat.card Nh := by rw [hNhcard]; exact hodd
  obtain ⟨Th, hTh, hBTh⟩ := exists_sylowOf_normalized_of_coprime (q := q) hBhp hBhN hNhp
  have hThle : Th ≤ Nh := hTh.le
  set T : Subgroup G := (Th.comap π).map X.subtype with hT
  have hTsub : T.subgroupOf X = Th.comap π := by
    rw [hT, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
  have hNhcomap : Nh.comap π = N' := Subgroup.comap_map_eq_self (hπker.le.trans hS'N')
  have hThN : Th.comap π ≤ N' := by
    rw [← hNhcomap]
    exact Subgroup.comap_mono hThle
  have hSTh : S ≤ T := by
    intro s hs
    refine ⟨⟨s, hSX hs⟩, ?_, rfl⟩
    show π ⟨s, hSX hs⟩ ∈ Th
    have : (⟨s, hSX hs⟩ : X) ∈ π.ker := by rw [hπker]; exact hs
    rw [MonoidHom.mem_ker.mp this]
    exact Th.one_mem
  have hTN : T ≤ N := by
    rintro _ ⟨y, hy, rfl⟩
    exact hThN hy
  have hBT : B ≤ normalizer (T : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    rintro b hb _ ⟨y, hy, rfl⟩
    refine ⟨⟨b, hBX hb⟩ * y * ⟨b, hBX hb⟩⁻¹, ?_, rfl⟩
    show π (⟨b, hBX hb⟩ * y * ⟨b, hBX hb⟩⁻¹) ∈ Th
    have hbB : π ⟨b, hBX hb⟩ ∈ Bh := ⟨⟨b, hBX hb⟩, hb, rfl⟩
    have := (mem_normalizer_iff.mp (hBTh hbB) (π y)).mp hy
    rwa [map_mul, map_mul, map_inv]
  refine ⟨T, hSTh, hTN, hBT, ?_, ?_⟩
  · have h1 : T.relIndex N = Th.relIndex Nh := by
      rw [← Subgroup.relIndex_subgroupOf hNX, hTsub, ← hN', Subgroup.relIndex_comap]
    rw [h1]
    exact (isSylowOf_iff.mp hTh).2.2
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := hTh.isPGroup (⟨π y, hy⟩ : Th)
    refine ⟨k, ?_⟩
    have h2 : π (y ^ (q ^ k)) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have h3 : y ^ (q ^ k) ∈ S' := by
      rw [← hπker]
      exact h2
    exact h3


def involClosure (Y : Subgroup G) : Subgroup G := closure {y | y ∈ Y ∧ y ^ 2 = 1}

omit [Finite G] in
theorem isElemAbelian_zpowers' {p : ℕ} {x : G} (hx : x ^ p = 1) : IsElemAbelian p (zpowers x) :=
  CFSG.Open.isElemAbelian_zpowers hx

omit [Finite G] in
theorem involClosure_le (Y : Subgroup G) : involClosure Y ≤ Y :=
  (Subgroup.closure_le Y).mpr fun _ hy => hy.1

theorem mem_normalizer_involClosure_of_forall {Y : Subgroup G} {g : G}
    (h : ∀ i ∈ Y, i ^ 2 = 1 → g * i * g⁻¹ ∈ Y) : g ∈ normalizer (involClosure Y : Set G) := by
  have h1 : (involClosure Y).map (MulAut.conj g).toMonoidHom ≤ involClosure Y := by
    rw [involClosure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, ⟨hyY, hy2⟩, rfl⟩
    refine subset_closure ⟨h y hyY hy2, ?_⟩
    change (g * y * g⁻¹) ^ 2 = 1
    rw [conj_pow, hy2]
    simp
  have h2 : (involClosure Y).map (MulAut.conj g).toMonoidHom = involClosure Y :=
    Subgroup.eq_of_le_of_card_ge h1 (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  exact mem_normalizer_iff_map_conj_eq.mpr h2

theorem mem_normalizer_involClosure {Y : Subgroup G} {g : G} (hg : g ∈ normalizer (Y : Set G)) :
    g ∈ normalizer (involClosure Y : Set G) :=
  mem_normalizer_involClosure_of_forall fun i hi _ => (mem_normalizer_iff.mp hg i).mp hi

theorem involClosure_ne_bot {Y : Subgroup G} (hY : IsPGroup 2 Y) (hY1 : Y ≠ ⊥) :
    involClosure Y ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card Y := by
    obtain ⟨n, hn⟩ := hY.exists_card_eq
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hn)) hY1
    · rw [hn]; exact dvd_pow_self 2 hn0.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Y) 2 hdvd
  intro hbot
  have hz1 : (z : G) ∈ involClosure Y := subset_closure ⟨z.2, by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this⟩
  rw [hbot, mem_bot] at hz1
  have : z = 1 := Subtype.ext hz1
  rw [this, orderOf_one] at hz
  exact absurd hz (by norm_num)


omit [Finite G] in
theorem le_normalizer_inf' {A B C : Subgroup G} (hB : A ≤ normalizer (B : Set G))
    (hC : A ≤ normalizer (C : Set G)) : A ≤ normalizer ((B ⊓ C : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro a ha g hg
  exact ⟨Subgroup.le_normalizer_iff.mp hB a ha g hg.1, Subgroup.le_normalizer_iff.mp hC a ha g hg.2⟩

theorem exists_mul_normalizer_of_isSylowOf {p : ℕ} [Fact p.Prime] {S O R : Subgroup G}
    (hS : IsSylowOf p S O) (hR : R ≤ normalizer (O : Set G)) {r : G} (hr : r ∈ R) :
    ∃ o ∈ O, ∃ m ∈ normalizer (S : Set G), r = o * m := by
  have hrn : r ∈ normalizer (O : Set G) := hR hr
  have hle : S.map (MulAut.conj r).toMonoidHom ≤ O := by
    rintro _ ⟨s, hs, rfl⟩
    exact (mem_normalizer_iff.mp hrn s).mp (hS.le hs)
  have hS' : IsSylowOf p (S.map (MulAut.conj r).toMonoidHom) O := by
    refine isSylowOf_of_card hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj r).injective]
    exact hS.card_eq
  obtain ⟨k, hk, hkey⟩ := hS.exists_mem_conj hS'
  refine ⟨k, hk, k⁻¹ * r, ?_, by group⟩
  rw [mem_normalizer_iff]
  intro b
  have h1 := hkey (r * b * r⁻¹)
  have h2 : r * b * r⁻¹ ∈ S.map (MulAut.conj r).toMonoidHom ↔ b ∈ S := by
    constructor
    · rintro ⟨b', hb', hbb'⟩
      have : b' = b := by simpa using hbb'
      rwa [← this]
    · intro hb
      exact ⟨b, hb, rfl⟩
  rw [← h2, h1]
  have : k⁻¹ * (r * b * r⁻¹) * k = k⁻¹ * r * b * (k⁻¹ * r)⁻¹ := by group
  rw [this]

theorem not_two_dvd_card_of_pow_three {Q : Type*} [Group Q] [Finite Q] (h : ∀ g : Q, g ^ 3 = 1) :
    ¬ 2 ∣ Nat.card Q := by
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 hdvd
  have := orderOf_dvd_of_pow_eq_one (h g)
  rw [hg] at this
  omega



theorem not_two_dvd_relIndex_inf {K O : Subgroup G} (hKO : K ≤ normalizer (O : Set G))
    (h3 : ∀ k ∈ K, k ^ 3 ∈ O) : ¬ 2 ∣ (K ⊓ O).relIndex K := by
  have hn : ((K ⊓ O).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (le_normalizer_inf' Subgroup.le_normalizer hKO)
  refine not_two_dvd_card_of_pow_three (Q := ↥K ⧸ (K ⊓ O).subgroupOf K) fun g => ?_
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr ⟨K.pow_mem k.2 3, h3 k k.2⟩

theorem exists_elemAbelian_three_normalizing_involClosure {O R Y A : Subgroup G} {x : G}
    (hOR : O ≤ R) (hRO : R ≤ normalizer (O : Set G))
    (hYR : Y ≤ normalizer (R : Set G)) (hYO : Y ≤ normalizer (O : Set G))
    (hO3 : ¬ 3 ∣ Nat.card O) (hR3 : ∀ r ∈ R, r ^ 3 ∈ O)
    (hRab : ∀ r ∈ R, ∀ r' ∈ R, r * r' * r⁻¹ * r'⁻¹ ∈ O)
    (hY2 : IsPGroup 2 Y) (hYO' : IsSylowOf 2 (Y ⊓ O) O)
    (hx3 : x ^ 3 = 1) (hxR : x ∉ R) (hxRn : x ∈ normalizer (R : Set G))
    (hxc : ∀ r ∈ R, x * r * x⁻¹ * r⁻¹ ∈ O) (hxY : x ∈ normalizer (Y : Set G))
    (hAR : A ≤ R) (hAO : A ⊓ O = ⊥) (hA : 9 ≤ Nat.card A)
    (hAfix : ∀ a ∈ A, ∀ i ∈ Y, i ^ 2 = 1 → a * i * a⁻¹ * i⁻¹ ∈ O) :
    ∃ E : Subgroup G, E ≤ normalizer (involClosure Y : Set G) ∧ E ≤ R ⊔ zpowers x ∧
      IsElemAbelian 3 E ∧ 27 ≤ Nat.card E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
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
      not_two_dvd_relIndex_inf (hNR.trans hRO) fun n hn => hR3 n (hNR hn)
    rw [← Subgroup.relIndex_mul_relIndex S (N ⊓ O) N hSNO inf_le_left]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
    · exact h2 h
    · exact h3 h
  obtain ⟨T, hST, hTN, hYT, hTidx, hT3⟩ := exists_normalized_sylow_mod (p := 2) (q := 3) hSN hNS
    hYS hYN hY2 hodd
  have hTR : T ≤ R := hTN.trans hNR
  have hTO : T ⊓ O = S := by
    refine le_antisymm ?_ (le_inf hST hSO)
    rintro t ⟨htT, htO⟩
    obtain ⟨k, hk⟩ := hT3 t htT
    have hd : orderOf t ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨t, htO⟩ : O)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (3 ^ k) (orderOf t) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        (fun h => hO3 (h.trans hd)))
    obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
    have htc : t = (t ^ (3 ^ k)) ^ c := hc.symm
    rw [htc]
    exact S.pow_mem hk c
  have hO'n : (O.subgroupOf R).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOR).mpr hRO
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
    have hRbar3 : IsPGroup 3 (R ⧸ O.subgroupOf R) := fun g => ⟨1, by
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective g
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (hR3 r r.2)⟩
    obtain ⟨a, ha⟩ := hRbar3.exists_card_eq
    set Tim : Subgroup (R ⧸ O.subgroupOf R) := (T.subgroupOf N).map φ with hTim
    have hTimidx : Tim.index ∣ T.relIndex N := Subgroup.index_map_dvd (T.subgroupOf N) hφsurj
    have hTim1 : Tim.index = 1 := by
      have hdvd : Tim.index ∣ 3 ^ a := ha ▸ Subgroup.index_dvd_card Tim
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      rcases Nat.eq_zero_or_pos b with rfl | hb0
      · simpa using hb
      · exfalso
        apply hTidx
        exact (dvd_pow_self 3 hb0.ne').trans (hb ▸ hTimidx)
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
  have hD9 : 9 ∣ Nat.card D := by
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
    have hRbar3 : IsPGroup 3 (R ⧸ O.subgroupOf R) := fun g => ⟨1, by
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective g
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (hR3 r r.2)⟩
    obtain ⟨a, ha⟩ := hRbar3.exists_card_eq
    have hcardA : Nat.card A = Nat.card ψA.range :=
      Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv
    have hge : 9 ≤ Nat.card φD.range :=
      hA.trans (hcardA ▸ Subgroup.card_le_of_le hrange)
    have hdvd : Nat.card φD.range ∣ 3 ^ a := ha ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hb2 : 2 ≤ b := by
      by_contra hlt
      have : b ≤ 1 := by omega
      have : 3 ^ b ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
      omega
    have h9 : 9 ∣ Nat.card φD.range := by
      rw [hb]
      exact (pow_dvd_pow 3 hb2 : 3 ^ 2 ∣ 3 ^ b)
    exact h9.trans (Subgroup.card_range_dvd φD)
  have hxY₁ : x ∈ normalizer (Y₁ : Set G) := mem_normalizer_involClosure hxY
  have hxD : x ∈ normalizer (D : Set G) :=
    le_normalizer_inf' (A := zpowers x) (zpowers_le.mpr hxRn)
      (zpowers_le.mpr (Subgroup.le_normalizer hxY₁)) (mem_zpowers x)
  set Dp : Subgroup G := D ⊔ zpowers x with hDp
  have hDDp : D ≤ Dp := le_sup_left
  have hxDp : zpowers x ≤ Dp := le_sup_right
  have hDpD : Dp ≤ normalizer (D : Set G) := sup_le Subgroup.le_normalizer (zpowers_le.mpr hxD)
  have hxp : IsPGroup 3 ((zpowers x).subgroupOf Dp) := by
    have : IsPGroup 3 (zpowers x) := by
      have hxo : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
      rcases (Nat.dvd_prime Nat.prime_three).mp hxo with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
    exact this.comap_subtype
  obtain ⟨Q3, hQ3⟩ := hxp.exists_le_sylow
  set P3 : Subgroup G := (Q3 : Subgroup Dp).map Dp.subtype with hP3
  have hP3s : IsSylowOf 3 P3 Dp := ⟨Q3, rfl⟩
  have hxP3 : x ∈ P3 := by
    have : (⟨x, hxDp (mem_zpowers x)⟩ : Dp) ∈ (Q3 : Subgroup Dp) :=
      hQ3 (Subgroup.mem_subgroupOf.mpr (mem_zpowers x))
    exact ⟨_, this, rfl⟩
  set D₃ : Subgroup G := P3 ⊓ D with hD₃
  have hD₃s : IsSylowOf 3 D₃ D := hP3s.inf_of_le_normalizer hDDp hDpD
  have hD₃D : D₃ ≤ D := inf_le_right
  have hD₃p : IsPGroup 3 D₃ := hD₃s.isPGroup
  have hD₃O : D₃ ⊓ O = ⊥ := by
    obtain ⟨n, hn⟩ := hD₃p.exists_card_eq
    exact (Subgroup.disjoint_of_coprime_natCard (by
      rw [hn]
      exact Nat.Coprime.pow_left n
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hO3))).eq_bot
  have hD₃9 : 9 ≤ Nat.card D₃ := by
    rw [hD₃s.card_eq]
    have hpos : Nat.card D ≠ 0 := Nat.card_pos.ne'
    have h2 : 2 ≤ (Nat.card D).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).mp (by simpa using hD9)
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (Nat.card D).factorization 3 := Nat.pow_le_pow_right (by norm_num) h2
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
  have hD₃el : IsElemAbelian 3 D₃ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun d hd => ?_⟩
    · have h1 : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ D₃ ⊓ O :=
        ⟨D₃.mul_mem (D₃.mul_mem (D₃.mul_mem a.2 b.2) (D₃.inv_mem a.2)) (D₃.inv_mem b.2),
          hRab a (hDR (hD₃D a.2)) b (hDR (hD₃D b.2))⟩
      rw [hD₃O, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact Subtype.ext h1
    · have h1 : d ^ 3 ∈ D₃ ⊓ O := ⟨D₃.pow_mem hd 3, hR3 d (hDR (hD₃D hd))⟩
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
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hD₃el
      (isElemAbelian_zpowers' hx3) hcommE, ?_⟩
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three D₃ hx3 hxnD₃
    (fun e he => (hxD₃ e he).symm)]
  omega


end CFSG.LocalAnalysis.RankFourTheoremC
