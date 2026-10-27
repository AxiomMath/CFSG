module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerCP1
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.ABGLocalTools CFSG.LocalCores CFSG.Quasithin.B6
open scoped commutatorElement

structure CPSetting (p : ℕ) {H : Type*} [Group H] (T M : Subgroup H) {ι : Type*}
    (L : ι → Subgroup H) : Prop where
  prime : p.Prime
  sylow : IsSylowOf p T ⊤
  T_le_M : T ≤ M
  M_lt : M < ⊤
  M_max : ∀ Y : Subgroup H, T ≤ Y → Y < ⊤ → Y ≤ M
  inj : Function.Injective L
  qs : ∀ i, CFSG.IsQuasisimple ↥(L i)
  comm : ∀ i j, i ≠ j → ⁅L i, L j⁆ = ⊥
  K_normal : (⨆ i, L i).Normal
  KT : (⨆ i, L i) ⊔ T = ⊤
  perm : ∀ t ∈ T, ∀ i, ∃ j, conjSub t (L i) = L j
  trans : ∀ i j, ∃ t ∈ T, conjSub t (L i) = L j

section Setting

variable {H : Type*} [Group H] {p : ℕ} {T M : Subgroup H} {ι : Type*} {L : ι → Subgroup H}

theorem CPSetting.pgroup_T (hS : CPSetting p T M L) : IsPGroup p ↥T := (hS.sylow).isPGroup

theorem CPSetting.centralizes (hS : CPSetting p T M L) {i j : ι} (h : i ≠ j) :
    L i ≤ Subgroup.centralizer (L j : Set H) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hS.comm i j h)

theorem CPSetting.mul_comm' (hS : CPSetting p T M L) {i j : ι} (h : i ≠ j) {a b : H}
    (ha : a ∈ L i) (hb : b ∈ L j) : a * b = b * a :=
  ((Subgroup.mem_centralizer_iff.1 (hS.centralizes h ha)) b hb).symm

theorem CPSetting.K_le_normalizer (hS : CPSetting p T M L) (i : ι) :
    (⨆ j, L j) ≤ Subgroup.normalizer (L i : Set H) := by
  refine iSup_le fun j => ?_
  by_cases hij : j = i
  · subst hij
    exact Subgroup.le_normalizer
  · exact (hS.centralizes hij).trans (Subgroup.centralizer_le_normalizer _)

theorem CPSetting.T_le_normalizer_K (hS : CPSetting p T M L) :
    T ≤ Subgroup.normalizer ((⨆ j, L j : Subgroup H) : Set H) := by
  have : Subgroup.normalizer ((⨆ j, L j : Subgroup H) : Set H) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.2 hS.K_normal
  rw [this]
  exact le_top

theorem CPSetting.L_ne_bot (hS : CPSetting p T M L) (i : ι) : L i ≠ ⊥ := by
  have := isQuasisimple_nontrivial (hS.qs i)
  exact (Subgroup.nontrivial_iff_ne_bot _).1 this

theorem CPSetting.K_ne_bot [Nonempty ι] (hS : CPSetting p T M L) : (⨆ j, L j : Subgroup H) ≠ ⊥ := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  intro h
  exact hS.L_ne_bot i (eq_bot_iff.2 (h ▸ le_iSup L i))

theorem CPSetting.K_perfect (hS : CPSetting p T M L) :
    ⁅(⨆ i, L i : Subgroup H), (⨆ i, L i : Subgroup H)⁆ = (⨆ i, L i : Subgroup H) := by
  apply le_antisymm
  · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
      (Subgroup.inv_mem _ hb)
  · refine iSup_le fun i => ?_
    calc L i = ⁅L i, L i⁆ := (Subgroup.isPerfect_iff.1 (hS.qs i).1).symm
      _ ≤ _ := Subgroup.commutator_mono (le_iSup L i) (le_iSup L i)

theorem center_map_eq (K : Subgroup H) :
    (Subgroup.center ↥K).map K.subtype = K ⊓ Subgroup.centralizer (K : Set H) := by
  ext z
  constructor
  · rintro ⟨z0, hz0, rfl⟩
    refine ⟨z0.2, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz0 ⟨g, hg⟩)
  · rintro ⟨hzK, hzc⟩
    refine ⟨⟨z, hzK⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hzc) g g.2)

theorem CPSetting.inf_lt (hS : CPSetting p T M L) (i₀ : ι) : M ⊓ L i₀ < L i₀ := by
  refine lt_of_le_of_ne inf_le_right fun h => ?_
  have hLM : L i₀ ≤ M := h ▸ inf_le_left
  have hall : ∀ j, L j ≤ M := by
    intro j
    obtain ⟨t, ht, hconj⟩ := hS.trans i₀ j
    rw [← hconj]
    calc conjSub t (L i₀) ≤ conjSub t M := (conjSub t).monotone hLM
      _ = M := conjSub_eq_self (Subgroup.le_normalizer (hS.T_le_M ht))
  have hKM : (⨆ j, L j : Subgroup H) ≤ M := iSup_le hall
  have : (⨆ j, L j : Subgroup H) ⊔ T ≤ M := sup_le hKM hS.T_le_M
  rw [hS.KT] at this
  exact hS.M_lt.not_ge this

theorem CPSetting.normalizer_eq (hS : CPSetting p T M L) (i₀ : ι) :
    Subgroup.normalizer (L i₀ : Set H) =
      (⨆ i, L i : Subgroup H) ⊔ (T ⊓ Subgroup.normalizer (L i₀ : Set H)) := by
  apply le_antisymm
  · intro h hh
    have hh' : h ∈ (⨆ i, L i : Subgroup H) ⊔ T := by rw [hS.KT]; trivial
    obtain ⟨k, hk, t, ht, rfl⟩ := exists_mul_of_mem_sup hS.T_le_normalizer_K hh'
    have hkN := hS.K_le_normalizer i₀ hk
    have htN : t ∈ Subgroup.normalizer (L i₀ : Set H) := by
      have := (Subgroup.normalizer (L i₀ : Set H)).mul_mem
        ((Subgroup.normalizer (L i₀ : Set H)).inv_mem hkN) hh
      simpa using this
    exact Subgroup.mul_mem_sup hk ⟨ht, htN⟩
  · exact sup_le (hS.K_le_normalizer i₀) inf_le_right

variable [Finite H]

theorem center_le_of_unique_max {K T M : Subgroup H} (hp : p.Prime) (hKn : K.Normal)
    (hKperf : ⁅K, K⁆ = K) (hKne : K ≠ ⊥) (hT : IsPGroup p ↥T)
    (hmax : ∀ Y : Subgroup H, T ≤ Y → Y < ⊤ → Y ≤ M) :
    K ⊓ Subgroup.centralizer (K : Set H) ≤ M := by
  have := Fact.mk hp
  set Z : Subgroup H := K ⊓ Subgroup.centralizer (K : Set H) with hZ
  have hZn : Z.Normal := by
    refine ⟨fun z hz h => ?_⟩
    refine ⟨hKn.conj_mem z hz.1 h, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro k hk
    have hk' : h⁻¹ * k * h ∈ K := by simpa using hKn.conj_mem k hk h⁻¹
    have hc := Subgroup.mem_centralizer_iff.1 hz.2 _ hk'
    calc k * (h * z * h⁻¹) = h * ((h⁻¹ * k * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * k * h)) * h⁻¹ := by rw [hc]
      _ = h * z * h⁻¹ * k := by group
  by_contra hZM
  have htop : Z ⊔ T = ⊤ := by
    by_contra hne
    exact hZM (le_sup_left.trans (hmax _ le_sup_right (lt_top_iff_ne_top.2 hne)))
  have hTnZ : T ≤ Subgroup.normalizer (Z : Set H) := by
    have : Subgroup.normalizer (Z : Set H) = ⊤ := Subgroup.normalizer_eq_top_iff.2 hZn
    rw [this]
    exact le_top
  have hdecomp : ∀ k ∈ K, ∃ z ∈ Z, ∃ t ∈ T ⊓ K, k = z * t := by
    intro k hk
    have hk' : k ∈ Z ⊔ T := by rw [htop]; trivial
    obtain ⟨z, hz, t, ht, rfl⟩ := exists_mul_of_mem_sup hTnZ hk'
    refine ⟨z, hz, t, ⟨ht, ?_⟩, rfl⟩
    have : t = z⁻¹ * (z * t) := by group
    rw [this]
    exact K.mul_mem (K.inv_mem hz.1) hk
  let Zk : Subgroup ↥K := Subgroup.center ↥K
  let φ : ↥(T ⊓ K) →* (↥K ⧸ Zk) :=
    (QuotientGroup.mk' Zk).comp (Subgroup.inclusion (inf_le_right : T ⊓ K ≤ K))
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨z, hz, t, ht, hkt⟩ := hdecomp k k.2
    refine ⟨⟨t, ht⟩, ?_⟩
    show (QuotientGroup.mk (⟨t, ht.2⟩ : ↥K) : ↥K ⧸ Zk) = QuotientGroup.mk k
    rw [QuotientGroup.eq, Subgroup.mem_center_iff]
    intro g
    have hzt : t * z = z * t := (Subgroup.mem_centralizer_iff.1 hz.2) t ht.2
    have h1 : ((⟨t, ht.2⟩ : ↥K)⁻¹ * k : ↥K) = ⟨z, hz.1⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hkt]
      rw [← hzt]
      group
    rw [h1]
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hz.2) g g.2)
  have hQp : IsPGroup p (↥K ⧸ Zk) := (hT.to_le (inf_le_left : T ⊓ K ≤ T)).of_surjective φ hφ
  have hperf : commutator (↥K ⧸ Zk) = ⊤ := by
    have hK' : commutator ↥K = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hKperf)
    have hsurj := QuotientGroup.mk'_surjective Zk
    have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥K) ⊤ (QuotientGroup.mk' Zk)
    rw [Subgroup.map_top_of_surjective _ hsurj] at h1
    rw [_root_.commutator_def, ← h1, ← _root_.commutator_def, hK',
      Subgroup.map_top_of_surjective _ hsurj]
  have hnil : Group.IsNilpotent (↥K ⧸ Zk) := hQp.isNilpotent
  have hsubsing : Subsingleton (↥K ⧸ Zk) := by
    by_contra hne
    have : Nontrivial (↥K ⧸ Zk) := not_subsingleton_iff_nontrivial.1 hne
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (↥K ⧸ Zk)).ne hperf
  have hKc : K ≤ Subgroup.centralizer (K : Set H) := by
    intro k hk
    have h1 : (QuotientGroup.mk ⟨k, hk⟩ : ↥K ⧸ Zk) = 1 := Subsingleton.elim _ _
    have hmem : (⟨k, hk⟩ : ↥K) ∈ Zk := (QuotientGroup.eq_one_iff _).1 h1
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hmem ⟨g, hg⟩)
  have hbot : ⁅K, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hKc
  rw [hKperf] at hbot
  exact hKne hbot

theorem CPSetting.center_le_M [Nonempty ι] (hS : CPSetting p T M L) :
    (⨆ i, L i : Subgroup H) ⊓ Subgroup.centralizer ((⨆ i, L i : Subgroup H) : Set H) ≤ M :=
  center_le_of_unique_max hS.prime hS.K_normal hS.K_perfect hS.K_ne_bot hS.pgroup_T hS.M_max

theorem CPSetting.sylow_K (hS : CPSetting p T M L) :
    IsSylowOf p (T ⊓ (⨆ i, L i : Subgroup H)) (⨆ i, L i : Subgroup H) := by
  have := Fact.mk hS.prime
  have hn : (⊤ : Subgroup H) ≤ Subgroup.normalizer ((⨆ i, L i : Subgroup H) : Set H) := by
    have : Subgroup.normalizer ((⨆ i, L i : Subgroup H) : Set H) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.2 hS.K_normal
    rw [this]
  exact IsSylowOf.inf_of_le_normalizer hS.sylow le_top hn

theorem CPSetting.sylow_L (hS : CPSetting p T M L) (i : ι) : IsSylowOf p (T ⊓ L i) (L i) := by
  have := Fact.mk hS.prime
  have h := IsSylowOf.inf_of_le_normalizer hS.sylow_K (le_iSup L i) (hS.K_le_normalizer i)
  have e : (T ⊓ (⨆ j, L j : Subgroup H)) ⊓ L i = T ⊓ L i := by
    rw [inf_assoc, inf_eq_right.2 (le_iSup L i)]
  rwa [e] at h

theorem CPSetting.sylow_TL (hS : CPSetting p T M L) (i₀ : ι) :
    IsSylowOf p (T ⊓ Subgroup.normalizer (L i₀ : Set H)) (Subgroup.normalizer (L i₀ : Set H)) := by
  have := Fact.mk hS.prime
  have hKn := hS.K_normal
  rw [isSylowOf_iff]
  refine ⟨inf_le_right, hS.pgroup_T.to_le inf_le_left, ?_⟩
  have hNL := hS.normalizer_eq i₀
  have hKN := hS.K_le_normalizer i₀
  have hTK : T ⊓ Subgroup.normalizer (L i₀ : Set H) ⊓ (⨆ i, L i : Subgroup H) =
      T ⊓ (⨆ i, L i : Subgroup H) :=
    le_antisymm (fun x hx => ⟨hx.1.1, hx.2⟩) (fun x hx => ⟨⟨hx.1, hKN hx.2⟩, hx.2⟩)
  generalize T ⊓ Subgroup.normalizer (L i₀ : Set H) = TL at hNL hTK ⊢
  rw [hNL, relIndex_sup_eq_relIndex_of_normal, ← Subgroup.inf_relIndex_right, hTK]
  exact (isSylowOf_iff.1 hS.sylow_K).2.2

theorem CPSetting.sylow_HL (hS : CPSetting p T M L) (i₀ : ι) :
    IsSylowOf p (T ⊓ Subgroup.normalizer (L i₀ : Set H))
      (L i₀ ⊔ (T ⊓ Subgroup.normalizer (L i₀ : Set H))) := by
  have := Fact.mk hS.prime
  exact (hS.sylow_TL i₀).of_le le_sup_right (sup_le Subgroup.le_normalizer inf_le_right)

theorem CPSetting.T_inf_K [Finite ι] (hS : CPSetting p T M L) :
    T ⊓ (⨆ i, L i : Subgroup H) = ⨆ i, T ⊓ L i := by
  classical
  have := Fact.mk hS.prime
  have := Fintype.ofFinite ι
  have hdvd := relIndex_iSup_dvd_prod L (fun i => T ⊓ L i)
    (fun i j hij a ha b hb => hS.mul_comm' hij ha hb) (fun i => inf_le_right)
  have hnd : ¬ p ∣ ∏ i, (T ⊓ L i).relIndex (L i) := by
    intro h
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hS.prime.prime _).1 h
    exact (isSylowOf_iff.1 (hS.sylow_L i)).2.2 hi
  have hpg : IsPGroup p ↥(⨆ i, T ⊓ L i) := hS.pgroup_T.to_le (iSup_le fun i => inf_le_left)
  have hS' : IsSylowOf p (⨆ i, T ⊓ L i) (⨆ i, L i : Subgroup H) := by
    rw [isSylowOf_iff]
    exact ⟨iSup_le fun i => inf_le_right.trans (le_iSup L i), hpg, fun hd => hnd (hd.trans hdvd)⟩
  exact hS'.eq_of_le (iSup_le fun i => inf_le_inf_left T (le_iSup L i)) inf_le_right
    (hS.pgroup_T.to_le inf_le_left)

end Setting

end CFSG.QuasithinUnique.Setup.Layer
