module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Inputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFAbs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSimple
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Setup
public import CFSG.Quasithin.Background.AutOnElemAb

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.Quasithin Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem conj_mem_centralizer' {Y : Subgroup G} {g c : G} (hg : g ∈ normalizer (Y : Set G))
    (hc : c ∈ centralizer (Y : Set G)) : g * c * g⁻¹ ∈ centralizer (Y : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  have h := hc _ ((mem_normalizer_iff''.mp hg y).mp hy)
  calc y * (g * c * g⁻¹) = g * (g⁻¹ * y * g * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
    _ = g * c * g⁻¹ * y := by group

theorem uCore_le_pCoreOf_inf_centralizer_of_h1 {M T : Subgroup G}
    (h1 : M ⊓ centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    uCore M T ≤ pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) := by
  have hX := omegaOneCenterIn_le_inf_centralizer T
  have hMQ : M ≤ normalizer (pCoreOf 2 M : Set G) := localGroup_le_normalizer_pCoreOf 2 M
  have hQT : pCoreOf 2 M ≤ T := by
    have hsup := hT.isPGroup.to_sup_of_normal_right' (pCoreOf_isPGroup 2 M) (hT.le.trans hMQ)
    exact sup_eq_left.mp (hT.eq_of_le le_sup_left (sup_le hT.le (pCoreOf_le 2 M)) hsup)
  have hXC : CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ centralizer (pCoreOf 2 M : Set G) :=
    fun x hx => centralizer_le hQT ((hX hx).2)
  have hXQ : CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ pCoreOf 2 M := fun x hx =>
    h1 ⟨hT.le (hX hx).1, hXC hx⟩
  refine iSup_le fun m => ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨(mem_normalizer_iff.mp (hMQ m.2) x).mp (hXQ hx), conj_mem_centralizer' (hMQ m.2) (hXC hx)⟩


theorem isElemAbelian_uCore_of_h1 {M T : Subgroup G}
    (h1 : M ⊓ centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : IsElemAbelian 2 (uCore M T) := by
  have hX := omegaOneCenterIn_le_inf_centralizer T
  have hXe : IsElemAbelian 2 (CFSG.RankThree.PartOne.omegaOneCenterIn T) :=
    ⟨⟨⟨fun a b => Subtype.ext ((CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp
      b.2).2.1 a (hX a.2).1)⟩⟩,
      fun x hx => (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hx).2.2⟩
  have hY := uCore_le_pCoreOf_inf_centralizer_of_h1 h1 hT
  have hcomm : ∀ a ∈ uCore M T, ∀ b ∈ uCore M T, a * b = b * a :=
    fun a ha b hb => (hY hb).2 a (hY ha).1
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun y hy => ?_⟩
  change y ∈ (⨆ m : M, (CFSG.RankThree.PartOne.omegaOneCenterIn T).map
    (MulAut.conj (m : G)).toMonoidHom : Subgroup G) at hy
  refine (Subgroup.iSup_induction _ (C := fun y => y ∈ uCore M T ∧ y ^ 2 = 1) hy
    (fun m x hx => ?_) ⟨one_mem _, one_pow 2⟩ (fun a b ha hb => ?_)).2
  · obtain ⟨x₀, hx₀, rfl⟩ := hx
    refine ⟨mem_iSup_of_mem m ⟨x₀, hx₀, rfl⟩, ?_⟩
    simpa using congrArg (MulAut.conj (m : G)).toMonoidHom (hXe.2 x₀ hx₀)
  · have hab : Commute a b := hcomm a ha.1 b hb.1
    exact ⟨mul_mem ha.1 hb.1, by rw [hab.mul_pow, ha.2, hb.2, one_mul]⟩

theorem uCore_le_M_of_h1 {M T : Subgroup G}
    (h1 : M ⊓ centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : uCore M T ≤ M :=
  ((uCore_le_pCoreOf_inf_centralizer_of_h1 h1 hT).trans inf_le_left).trans (pCoreOf_le 2 M)

theorem pCoreOf_le_centralizer_uCore {M T : Subgroup G}
    (h1 : M ⊓ centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    pCoreOf 2 M ≤ centralizer (uCore M T : Set G) := fun x hx =>
  mem_centralizer_iff.mpr fun v hv =>
    ((uCore_le_pCoreOf_inf_centralizer_of_h1 h1 hT hv).2 x hx).symm


theorem inf_centralizer_subgroupOf_eq_pCore {M V L : Subgroup G} (hLM : L ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) (hML : M ≤ normalizer (L : Set G))
    (hO2 : pCoreOf 2 M ≤ centralizer (V : Set G))
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) (hnc : ¬ L ≤ centralizer (V : Set G)) :
    (L ⊓ centralizer (V : Set G)).subgroupOf L = CFSG.pCore 2 ↥L := by
  set K := (L ⊓ centralizer (V : Set G)).subgroupOf L with hK
  have hpc : pCoreOf 2 L ≤ pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLM)
      (hML.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (pCoreOf_isPGroup 2 L)
  have hle : CFSG.pCore 2 ↥L ≤ K := by
    intro x hx
    rw [hK, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨x.2, hO2 (hpc ⟨x, hx, rfl⟩)⟩
  have hnorm : K.Normal := ⟨fun k hk g => by
    rw [hK, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hk ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 hk.1) (L.inv_mem g.2), ?_⟩
    exact conj_mem_centralizer' (hMV (hLM g.2)) hk.2⟩
  haveI := hnorm
  haveI : (K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
    hnorm.map _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with
    h | h
  · refine le_antisymm (fun x hx => ?_) hle
    have : QuotientGroup.mk' (CFSG.pCore 2 ↥L) x ∈ K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  · exfalso
    apply hnc
    intro l hl
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨l, hl⟩ ∈
        K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨k, hkK, hk⟩ := Subgroup.mem_map.mp hmem
    have h2 : k⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := QuotientGroup.eq.mp hk
    have h3 : (⟨l, hl⟩ : ↥L) = k * (k⁻¹ * ⟨l, hl⟩) := by simp
    have : (⟨l, hl⟩ : ↥L) ∈ K := by rw [h3]; exact K.mul_mem hkK (hle h2)
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).2


theorem exists_mem_orderOf_eq_of_one_le_pRank {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (h : 1 ≤ CFSG.Open.pRank p H) : ∃ x ∈ H, orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hne
  push Not at hne
  have hS : sSup {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k} = 0 := by
    refine Nat.eq_zero_of_le_zero (csSup_le' fun k hk => ?_)
    obtain ⟨E, hEH, hE, hcard⟩ := hk
    by_contra hk0
    have hk0' : k ≠ 0 := by omega
    have hE1 : E ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card E = 1 := by rw [hbot]; exact Subgroup.card_bot
      rw [hcard] at h1
      have := Nat.one_lt_pow hk0' hp.one_lt
      omega
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hE1
    have hxp : (x : G) ^ p = 1 := hE.2 x x.2
    have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    exact hne (x : G) (hEH x.2) (orderOf_eq_prime hxp hx1')
  have : 1 ≤ sSup {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k} := h
  omega

theorem exists_maxElemAbelian_noncomm {M V L : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hLM : L ≤ M) (hMV : M ≤ normalizer (V : Set G)) (hML : M ≤ normalizer (L : Set G))
    (hLdef : ∀ x ∈ M, (∃ k : ℕ, orderOf x = p ^ k) → x ∈ L)
    (hker : (L ⊓ centralizer (V : Set G)).subgroupOf L = CFSG.pCore 2 ↥L)
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hna : ∃ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b ≠ b * a)
    (hJ : 1 ≤ CFSG.Open.pRank p (CFSG.Quasithin.thompsonJ M)) :
    ∃ A : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian M A ∧
      ∃ a ∈ A, ∃ l ∈ L, a * l * a⁻¹ * l⁻¹ ∉ centralizer (V : Set G) := by
  by_contra H
  push Not at H
  obtain ⟨x, hxJ, hxo⟩ := exists_mem_orderOf_eq_of_one_le_pRank hp hJ
  have hxM : x ∈ M := by
    refine (iSup₂_le (fun A hA => hA.1) : CFSG.Quasithin.thompsonJ M ≤ M) hxJ
  have hxL : x ∈ L := hLdef x hxM ⟨1, by simpa using hxo⟩
  have key : ∀ g ∈ CFSG.Quasithin.thompsonJ M, g ∈ M ∧
      ∀ l ∈ L, g * l * g⁻¹ * l⁻¹ ∈ centralizer (V : Set G) := by
    intro g hg
    refine Subgroup.iSup_induction _ (C := fun g => g ∈ M ∧
      ∀ l ∈ L, g * l * g⁻¹ * l⁻¹ ∈ centralizer (V : Set G)) hg (fun A y hy => ?_)
      ⟨M.one_mem, fun l _ => by simp⟩ (fun g₁ g₂ h₁ h₂ => ?_)
    · by_cases hA : CFSG.Quasithin.IsMaxElemAbelian M A
      · rw [iSup_pos hA] at hy
        exact ⟨hA.1 hy, fun l hl => H A hA y hy l hl⟩
      · rw [iSup_neg hA, Subgroup.mem_bot] at hy
        subst hy
        exact ⟨M.one_mem, fun l _ => by simp⟩
    · refine ⟨M.mul_mem h₁.1 h₂.1, fun l hl => ?_⟩
      have hc := conj_mem_centralizer' (hMV h₁.1) (h₂.2 l hl)
      have := mul_mem hc (h₁.2 l hl)
      have heq : g₁ * g₂ * l * (g₁ * g₂)⁻¹ * l⁻¹ =
          g₁ * (g₂ * l * g₂⁻¹ * l⁻¹) * g₁⁻¹ * (g₁ * l * g₁⁻¹ * l⁻¹) := by group
      rw [heq]
      exact this
  have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  have hxP : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    have hcen : QuotientGroup.mk (s := CFSG.pCore 2 ↥L) ⟨x, hxL⟩ ∈
        Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
      have hmem : (⟨x, hxL⟩ * l * ⟨x, hxL⟩⁻¹ * l⁻¹ : ↥L) ∈ CFSG.pCore 2 ↥L := by
        rw [← hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        refine ⟨(⟨x, hxL⟩ * l * ⟨x, hxL⟩⁻¹ * l⁻¹ : ↥L).2, ?_⟩
        simpa using (key x hxJ).2 l l.2
      have := (QuotientGroup.eq_one_iff _).mpr hmem
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hZ, Subgroup.mem_bot] at hcen
    exact (QuotientGroup.eq_one_iff _).mp hcen
  have hxmem : x ∈ pCoreOf 2 L := ⟨⟨x, hxL⟩, hxP, rfl⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨x, hxmem⟩
  have hdvd : p ∣ 2 ^ k := by
    rw [← hxo]
    exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))


section Action

open scoped IsMulCommutative

@[expose] noncomputable def actAut (L V : Subgroup G) (hL : L ≤ normalizer (V : Set G)) :
    ↥L →* MulAut ↥V :=
  (conjAct V).comp (Subgroup.inclusion hL)

theorem coe_actAut_apply {L V : Subgroup G} (hL : L ≤ normalizer (V : Set G)) (l : ↥L) (v : ↥V) :
    ((actAut L V hL l v : ↥V) : G) = (l : G) * (v : G) * (l : G)⁻¹ :=
  AutOn.coe_conjAct_apply V (Subgroup.inclusion hL l) v

theorem range_actAut (L V : Subgroup G) (hL : L ≤ normalizer (V : Set G)) :
    (actAut L V hL).range = autOn L V := by
  unfold actAut autOn
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

theorem ker_actAut (L V : Subgroup G) (hL : L ≤ normalizer (V : Set G)) :
    (actAut L V hL).ker = (L ⊓ centralizer (V : Set G)).subgroupOf L := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have h := AutOn.conjAct_eq_one_iff (V := V) (Subgroup.inclusion hL a)
  change conjAct V (Subgroup.inclusion hL a) = 1 ↔ _ at h
  exact ⟨fun h1 => ⟨a.2, (h.mp h1)⟩, fun h1 => h.mpr h1.2⟩

theorem mem_autOn_of_mem {L V : Subgroup G} (hL : L ≤ normalizer (V : Set G)) (l : ↥L) :
    actAut L V hL l ∈ autOn L V := by
  rw [← range_actAut L V hL]; exact ⟨l, rfl⟩

@[expose] noncomputable def actOn (L V : Subgroup G) (hL : L ≤ normalizer (V : Set G)) :
    ↥L →* ↥(autOn L V) :=
  (actAut L V hL).codRestrict (autOn L V) (mem_autOn_of_mem hL)

theorem actOn_surjective (L V : Subgroup G) (hL : L ≤ normalizer (V : Set G)) :
    Function.Surjective (actOn L V hL) := by
  rintro ⟨x, hx⟩
  rw [← range_actAut L V hL] at hx
  obtain ⟨l, rfl⟩ := hx
  exact ⟨l, rfl⟩

theorem ker_actOn (L V : Subgroup G) (hL : L ≤ normalizer (V : Set G)) :
    (actOn L V hL).ker = (L ⊓ centralizer (V : Set G)).subgroupOf L := by
  rw [← ker_actAut L V hL]
  ext a
  simp [actOn, MonoidHom.mem_ker, Subtype.ext_iff]

theorem coe_actOn_apply {L V : Subgroup G} (hL : L ≤ normalizer (V : Set G)) (l : ↥L) (v : ↥V) :
    (((actOn L V hL l : ↥(autOn L V)) : MulAut ↥V) v : G) = (l : G) * (v : G) * (l : G)⁻¹ :=
  coe_actAut_apply hL l v

theorem relIndex_autOn_inf_centSub {A V : Subgroup G} [IsMulCommutative ↥V]
    (hAN : A ≤ normalizer (V : Set G)) (Y : Subgroup ↥V) :
    (autOn A V ⊓ centSub Y).relIndex (autOn A V) =
      (A ⊓ centralizer ((Y.map V.subtype : Subgroup G) : Set G)).relIndex A := by
  set f := actAut A V hAN with hf
  have hrange : f.range = autOn A V := range_actAut A V hAN
  set D : Subgroup ↥A := (centSub Y).comap f with hD
  have hkerD : f.ker ≤ D := fun a ha => by
    rw [hD, Subgroup.mem_comap, MonoidHom.mem_ker.mp ha]; exact (centSub Y).one_mem
  have h1 : autOn A V ⊓ centSub Y = D.map f := by
    rw [hD, Subgroup.map_comap_eq, hrange, inf_comm]
  have h2 : autOn A V = (⊤ : Subgroup ↥A).map f := by
    rw [← hrange, MonoidHom.range_eq_map]
  have h3 : (A ⊓ centralizer ((Y.map V.subtype : Subgroup G) : Set G)).subgroupOf A = D := by
    ext a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, hD, Subgroup.mem_comap, mem_centSub,
      mem_centralizer_iff]
    constructor
    · rintro ⟨-, hc⟩ y hy
      apply Subtype.ext
      rw [hf, coe_actAut_apply]
      have := hc (y : G) ⟨y, hy, rfl⟩
      calc (a : G) * y * (a : G)⁻¹ = (y * a) * (a : G)⁻¹ := by rw [← this]
        _ = y := by group
    · intro h
      refine ⟨a.2, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      have := congrArg (fun z : ↥V => (z : G)) (h y hy)
      simp only [hf, coe_actAut_apply] at this
      calc (y : G) * a = ((a : G) * y * (a : G)⁻¹) * a := by rw [this]
        _ = a * y := by group
  have h4 : (D.map f).relIndex ((⊤ : Subgroup ↥A).map f) =
      (D ⊔ f.ker).relIndex ((⊤ : Subgroup ↥A) ⊔ f.ker) := Subgroup.relIndex_map_map f D ⊤
  rw [h1, h2, h4, top_sup_eq, Subgroup.relIndex_top_right, sup_eq_left.mpr hkerD,
    Subgroup.relIndex, h3]

end Action


section Assembly

open scoped IsMulCommutative

omit [Finite G] in
theorem isElemAbelian_mono' {V Y : Subgroup G} (hV : IsElemAbelian 2 V) (hYV : Y ≤ V) :
    IsElemAbelian 2 Y :=
  ⟨⟨⟨fun a b => Subtype.ext (by
    have := hV.1
    exact setLike_mul_comm (hYV a.2) (hYV b.2))⟩⟩, fun y hy => hV.2 y (hYV hy)⟩

theorem offender_autOn {M V A : Subgroup G} [IsMulCommutative ↥V] (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hVM : V ≤ M) (hAM : A ≤ M) (hMV : M ≤ normalizer (V : Set G))
    (hA : CFSG.Quasithin.IsMaxElemAbelian M A) (Y : Subgroup ↥V) :
    Nat.card Y ≤ (autOn A V ⊓ centSub Y).relIndex (autOn A V) *
      Nat.card ↥(Y ⊓ fixV (autOn A V)) := by
  have hAN : A ≤ normalizer (V : Set G) := hAM.trans hMV
  have hV : IsElemAbelian 2 V := ⟨inferInstance, hV2⟩
  set Y₀ : Subgroup G := Y.map V.subtype with hY₀
  have hY₀V : Y₀ ≤ V := fun g hg => by obtain ⟨y, -, rfl⟩ := hg; exact y.2
  have hY₀e : IsElemAbelian 2 Y₀ := isElemAbelian_mono' hV hY₀V
  have h1 := card_le_relIndex_mul_card hY₀e (hY₀V.trans hVM) hA
  have hc : Nat.card Y = Nat.card Y₀ := (Subgroup.card_map_of_injective V.subtype_injective).symm
  have hidx := relIndex_autOn_inf_centSub hAN Y
  have hfixeq : fixV (autOn A V) = (centralizer (A : Set G)).subgroupOf V :=
    AutOn.fixV_autOn_eq hAN
  have hmap : (Y ⊓ fixV (autOn A V)).map V.subtype = Y₀ ⊓ centralizer (A : Set G) := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.coe_subtype, hfixeq,
      Subgroup.mem_subgroupOf, hY₀]
    constructor
    · rintro ⟨y, ⟨hyY, hyc⟩, rfl⟩
      exact ⟨⟨y, hyY, rfl⟩, hyc⟩
    · rintro ⟨⟨y, hyY, rfl⟩, hgc⟩
      exact ⟨y, ⟨hyY, hgc⟩, rfl⟩
  have hfix : Nat.card ↥(Y ⊓ fixV (autOn A V)) = Nat.card ↥(Y₀ ⊓ centralizer (A : Set G)) := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective V.subtype_injective).symm
  rw [hc, hidx, hfix]
  exact h1

theorem isU4Group_autOn {n : ℕ} {L V : Subgroup G} [IsMulCommutative ↥V] (hLN : L ≤ normalizer (V : Set G))
    (hker : (L ⊓ centralizer (V : Set G)).subgroupOf L = CFSG.pCore 2 ↥L)
    (hshape : ∃ d : TauCeti.ValidLieTypeIndex,
      (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = n ∧ d.1 = .twistedA 3 q) ∧
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    IsU4Group n (autOn L V) := by
  obtain ⟨d, hd, ⟨e⟩⟩ := hshape
  have e₁ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(autOn L V) :=
    (QuotientGroup.quotientMulEquivOfEq
      (hker.symm.trans (ker_actOn L V hLN).symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (actOn L V hLN) (actOn_surjective L V hLN))
  exact ⟨d, hd, ⟨e₁.symm.trans e⟩⟩


theorem exists_u4OffenderData_of_setting {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M V : Subgroup G} [IsMulCommutative ↥V] (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hVM : V ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) (hO2 : pCoreOf 2 M ≤ centralizer (V : Set G))
    (hU : U4ShapeAt n p M)
    (hnc : ¬ CFSG.RankThree.PartOne.pElementSubgroup p M ≤ centralizer (V : Set G))
    (hJ : 2 ≤ CFSG.Open.pRank p (CFSG.Quasithin.thompsonJ M)) :
    (CFSG.RankThree.PartOne.pElementSubgroup p M ⊓ centralizer (V : Set G)).subgroupOf
        (CFSG.RankThree.PartOne.pElementSubgroup p M) =
      CFSG.pCore 2 ↥(CFSG.RankThree.PartOne.pElementSubgroup p M) ∧
    ∃ A : Subgroup G, A ≤ M ∧
      U4OffenderData n (autOn (CFSG.RankThree.PartOne.pElementSubgroup p M) V) (autOn A V) := by
  set L := CFSG.RankThree.PartOne.pElementSubgroup p M with hL
  obtain ⟨d, ⟨q, hq2, hqn, hd, hpq⟩, ⟨e⟩⟩ := hU
  have hLM : L ≤ M := pElementSubgroup_le p M
  have hML : M ≤ normalizer (L : Set G) := le_normalizer_pElementSubgroup p M
  haveI := u4Group_isSimple hq2 hd
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := e.isSimpleGroup
  have hna : ∃ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := u4Group_nonabelian hq2 hd
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hker := inf_centralizer_subgroupOf_eq_pCore hLM hMV hML hO2 hsimple hnc
  have hLdef : ∀ x ∈ M, (∃ k : ℕ, orderOf x = p ^ k) → x ∈ L := fun x hx hk =>
    Subgroup.subset_closure ⟨hx, hk⟩
  obtain ⟨A, hA, a, ha, l, hl, hnot⟩ := exists_maxElemAbelian_noncomm hp hp2 hLM hMV hML hLdef
    hker hsimple hna (by omega)
  refine ⟨hker, A, hA.1, ?_⟩
  have hAN : A ≤ normalizer (V : Set G) := hA.1.trans hMV
  refine ⟨isU4Group_autOn (hLM.trans hMV) hker ⟨d, ⟨q, hq2, hqn, hd⟩, ⟨e⟩⟩,
    AutOn.isElemAbelian2_autOn hA.2.1, AutOn.autOn_le_normalizer_autOn (hA.1.trans hML), ?_,
    fun Y _ => offender_autOn hV2 hVM hA.1 hMV hA Y⟩
  refine ⟨conjAct V ⟨a, hAN ha⟩, AutOn.conjAct_mem_autOn_of_mem (hAN ha) ha,
    conjAct V ⟨l, hLM.trans hMV hl⟩, AutOn.conjAct_mem_autOn_of_mem (hLM.trans hMV hl) hl, ?_⟩
  intro hcomm
  apply hnot
  have h1 : conjAct V (⟨a, hAN ha⟩ * ⟨l, hLM.trans hMV hl⟩ * (⟨a, hAN ha⟩)⁻¹ *
      (⟨l, hLM.trans hMV hl⟩)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  exact (AutOn.conjAct_eq_one_iff _).mp h1


@[expose] noncomputable def commEquiv {V L : Subgroup G} [IsMulCommutative ↥V]
    (hLN : L ≤ normalizer (V : Set G)) :
    ↥(commV (autOn L V)) ≃* ↥⁅V, L⁆ :=
  (MulEquiv.subgroupCongr (AutOn.commV_autOn_eq hLN)).trans
    (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer_iff_commutator_le_left.mp hLN))

theorem coe_commEquiv {V L : Subgroup G} [IsMulCommutative ↥V] (hLN : L ≤ normalizer (V : Set G))
    (u : ↥(commV (autOn L V))) : ((commEquiv hLN u : ↥⁅V, L⁆) : G) = ((u : ↥V) : G) := rfl

theorem coe_commEquiv_symm {V L : Subgroup G} [IsMulCommutative ↥V]
    (hLN : L ≤ normalizer (V : Set G)) (x : ↥⁅V, L⁆) :
    ((((commEquiv hLN).symm x : ↥(commV (autOn L V))) : ↥V) : G) = (x : G) := by
  have h := coe_commEquiv hLN ((commEquiv hLN).symm x)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem transfer_conclusion {V L : Subgroup G} [IsMulCommutative ↥V]
    (hLN : L ≤ normalizer (V : Set G)) {H : Type} [Group H] {X : Type} [AddCommGroup X]
    (act : H → X → X) (ε₀ : ↥(autOn L V) ≃* H)
    (φ₀ : ↥(commV (autOn L V)) →* Multiplicative X) (hφs : Function.Surjective φ₀)
    (hφk : φ₀.ker = (fixV (autOn L V)).subgroupOf (commV (autOn L V)))
    (heq : ∀ (l : ↥(autOn L V)) (u u' : ↥(commV (autOn L V))),
      (l : MulAut ↥V) (u : ↥V) = (u' : ↥V) →
        φ₀ u' = Multiplicative.ofAdd (act (ε₀ l) (Multiplicative.toAdd (φ₀ u)))) :
    ∃ (ε : ↥L →* H) (φ : ↥⁅V, L⁆ →* Multiplicative X), Function.Surjective ε ∧
      Function.Surjective φ ∧ ε.ker = (L ⊓ centralizer (V : Set G)).subgroupOf L ∧
      φ.ker = (⁅V, L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅V, L⁆ ∧
      ∀ (l : ↥L) (u u' : ↥⁅V, L⁆), (l : G) * (u : G) * (l : G)⁻¹ = (u' : G) →
        φ u' = Multiplicative.ofAdd (act (ε l) (Multiplicative.toAdd (φ u))) := by
  set θ := commEquiv (V := V) hLN with hθ
  refine ⟨ε₀.toMonoidHom.comp (actOn L V hLN), φ₀.comp θ.symm.toMonoidHom,
    ε₀.surjective.comp (actOn_surjective L V hLN), hφs.comp θ.symm.surjective, ?_, ?_, ?_⟩
  · rw [← ker_actOn L V hLN]
    ext a
    simp [MonoidHom.mem_ker]
  · ext x
    have h1 : x ∈ (φ₀.comp θ.symm.toMonoidHom).ker ↔ θ.symm x ∈ φ₀.ker := Iff.rfl
    rw [h1, hφk, Subgroup.mem_subgroupOf, AutOn.fixV_autOn_eq hLN, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, Subgroup.mem_inf, hθ, coe_commEquiv_symm]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  · intro l u u' h
    have hu : (actOn L V hLN l : MulAut ↥V) (θ.symm u : ↥V) = (θ.symm u' : ↥V) := by
      apply Subtype.ext
      rw [coe_actOn_apply, hθ, coe_commEquiv_symm, coe_commEquiv_symm]
      exact h
    exact heq (actOn L V hLN l) (θ.symm u) (θ.symm u') hu


theorem naturalU4ModuleConclusion_of_abstract {n : ℕ} {V L : Subgroup G} [IsMulCommutative ↥V]
    (hLN : L ≤ normalizer (V : Set G))
    (hker : (L ⊓ centralizer (V : Set G)).subgroupOf L = CFSG.pCore 2 ↥L)
    (h : NaturalU4Abstract n (autOn L V)) : NaturalU4ModuleConclusion n L V := by
  rcases h with ⟨F, hF, hFin, hcard, ε₀, φ₀, hs, hk, heq⟩ |
    ⟨F, hF, hFin, b, c, hcard, hirr, ε₀, φ₀, hs, hk, heq⟩
  · obtain ⟨ε, φ, hεs, hφs, hεk, hφk, hq⟩ := transfer_conclusion hLN
      (H := ↥(StatedSU 4 (2 ^ n) F))
      (fun (g : ↥(StatedSU 4 (2 ^ n) F)) x =>
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec x) ε₀ φ₀ hs hk heq
    exact Or.inl ⟨F, hF, hFin, hcard, ε, φ, hεs, hφs, hεk.trans hker, hφk, hq⟩
  · obtain ⟨ε, φ, hεs, hφs, hεk, hφk, hq⟩ := transfer_conclusion hLN
      (H := ↥(StatedOmega (StatedQuadMinus 3 F b c)))
      (fun (g : ↥(StatedOmega (StatedQuadMinus 3 F b c))) x =>
        ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec x)
      ε₀ φ₀ hs hk heq
    exact Or.inr ⟨F, hF, hFin, b, c, hcard, hirr, ε, φ, hεs, hφs, hεk.trans hker, hφk, hq⟩

end Assembly

open scoped IsMulCommutative in
theorem kFactAGL81I54U4_of_abstract (habs : PartAAbstract) : KFactAGL81I54U4 := by
  intro G _ _ p n M T hp hp2 h1 hT hU hnc hJ
  have hV := isElemAbelian_uCore_of_h1 h1 hT
  haveI : IsMulCommutative ↥(uCore M T) := hV.1
  have hVM := uCore_le_M_of_h1 h1 hT
  have hMV := le_normalizer_uCore M T
  have hO2 := pCoreOf_le_centralizer_uCore h1 hT
  obtain ⟨hker, A, hAM, hdata⟩ := exists_u4OffenderData_of_setting hp hp2
    (fun v hv => hV.2 v hv) hVM hMV hO2 hU hnc hJ
  have hexp : ∀ v : ↥(uCore M T), v ^ 2 = 1 := fun v => Subtype.ext (hV.2 v v.2)
  have habs' := habs ↥(uCore M T) hexp n _ _ hdata
  exact naturalU4ModuleConclusion_of_abstract
    ((pElementSubgroup_le p M).trans hMV) hker habs'

end CFSG.LocalAnalysis.RankThreeUC
