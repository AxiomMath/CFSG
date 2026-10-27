module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoreEmbedding
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {S T : Subgroup G}
    (hS : IsPGroup p S) (hTS : T < S) : ∃ x ∈ S, x ∈ normalizer (T : Set G) ∧ x ∉ T := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : T.subgroupOf S < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hTS.not_ge (subgroupOf_eq_top.mp h)
  obtain ⟨x, hx, hxT⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  rw [← subgroupOf_normalizer_eq hTS.le] at hx
  exact ⟨x, x.2, hx, hxT⟩

theorem ne_bot_of_isSylowOf_two {M T : Subgroup G} (hM : IsTwoLocal M)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : T ≠ ⊥ := by
  rintro rfl
  obtain ⟨R, hR1, hR2, hRM⟩ := hM
  have h2R : 2 ∣ Nat.card R :=
    hR2.card_eq_or_dvd.resolve_left fun h => hR1 (card_eq_one.mp h)
  have h2M : 2 ∣ Nat.card M := h2R.trans (card_dvd_of_le (hRM ▸ le_normalizer : R ≤ M))
  have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
  exact h (by rwa [relIndex_bot_left])

theorem isSylowOf_top_of_normalizer_le {p : ℕ} [Fact p.Prime] {M T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T M) (hN : normalizer (T : Set G) ≤ M) :
    CFSG.ABGLocalTools.IsSylowOf p T ⊤ := by
  obtain ⟨S, hTS⟩ := hT.isPGroup.exists_le_sylow
  have hST : (S : Subgroup G) ≤ T := by
    by_contra hne
    obtain ⟨x, hxS, hxN, hxT⟩ :=
      exists_mem_normalizer_not_mem S.isPGroup' (lt_of_le_not_ge hTS hne)
    have hQ := hT.eq_of_le (le_inf hTS Subgroup.le_normalizer) (inf_le_right.trans hN)
      S.isPGroup'.to_inf_left
    exact hxT (hQ ▸ ⟨hxS, hxN⟩)
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, hT.isPGroup, ?_⟩
  rw [Subgroup.relIndex_top_right, le_antisymm hTS hST]
  exact S.not_dvd_index

omit [Finite G] in
private theorem conj_mem_centralizer {Y : Subgroup G} {g c : G} (hg : g ∈ normalizer (Y : Set G))
    (hc : c ∈ centralizer (Y : Set G)) : g * c * g⁻¹ ∈ centralizer (Y : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  have h := hc _ ((mem_normalizer_iff''.mp hg y).mp hy)
  calc y * (g * c * g⁻¹) = g * (g⁻¹ * y * g * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
    _ = g * c * g⁻¹ * y := by group

theorem iSup_conj_le_pCoreOf_inf_centralizer (hchar : IsCharTwoType G) {M T X : Subgroup G}
    (hM : IsTwoLocal M) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hXT : X ≤ T)
    (hXZ : X ≤ centralizer (T : Set G)) :
    (⨆ m : M, X.map (MulAut.conj (m : G)).toMonoidHom) ≤
      pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) := by
  have hMQ : M ≤ normalizer (pCoreOf 2 M : Set G) := localGroup_le_normalizer_pCoreOf 2 M
  have hQT : pCoreOf 2 M ≤ T := by
    have hsup := hT.isPGroup.to_sup_of_normal_right' (pCoreOf_isPGroup 2 M) (hT.le.trans hMQ)
    exact sup_eq_left.mp (hT.eq_of_le le_sup_left (sup_le hT.le (pCoreOf_le 2 M)) hsup)
  have hXC : X ≤ centralizer (pCoreOf 2 M : Set G) := hXZ.trans (centralizer_le hQT)
  have hXQ : X ≤ pCoreOf 2 M :=
    charTwo_local_centralizing_subgroup_le_core hchar M hM X (hXT.trans hT.le) hXC
  refine iSup_le fun m => ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨(mem_normalizer_iff.mp (hMQ m.2) x).mp (hXQ hx), conj_mem_centralizer (hMQ m.2) (hXC hx)⟩

omit [Finite G] in
private theorem conj_mem_iSup_conj (M X : Subgroup G) {n : G} (hn : n ∈ M) {y : G}
    (hy : y ∈ ⨆ m : M, X.map (MulAut.conj (m : G)).toMonoidHom) :
    n * y * n⁻¹ ∈ ⨆ m : M, X.map (MulAut.conj (m : G)).toMonoidHom := by
  refine Subgroup.iSup_induction _ (C := fun y => n * y * n⁻¹ ∈
    ⨆ m : M, X.map (MulAut.conj (m : G)).toMonoidHom) hy (fun m x hx => ?_) ?_
    (fun x y hx hy => ?_)
  · obtain ⟨x₀, hx₀, rfl⟩ := hx
    refine mem_iSup_of_mem (⟨n * m, M.mul_mem hn m.2⟩ : M) ⟨x₀, hx₀, ?_⟩
    simp [mul_assoc]
  · simp
  · simpa [mul_assoc] using mul_mem hx hy

omit [Finite G] in
theorem le_normalizer_iSup_conj (M X : Subgroup G) :
    M ≤ normalizer ((⨆ m : M, X.map (MulAut.conj (m : G)).toMonoidHom : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => conj_mem_iSup_conj M X hn hy, fun hy => by
    simpa [mul_assoc] using conj_mem_iSup_conj M X (M.inv_mem hn) hy⟩

theorem isElemAbelian_iSup_conj (hchar : IsCharTwoType G) {M T X : Subgroup G}
    (hM : IsTwoLocal M) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hXT : X ≤ T)
    (hXZ : X ≤ centralizer (T : Set G)) (hX : IsElemAbelian 2 X) :
    IsElemAbelian 2 (⨆ m : M, X.map (MulAut.conj (m : G)).toMonoidHom) := by
  have hY := iSup_conj_le_pCoreOf_inf_centralizer hchar hM hT hXT hXZ
  have hcomm : ∀ a ∈ (⨆ m : M, X.map (MulAut.conj (m : G)).toMonoidHom), ∀ b ∈
      (⨆ m : M, X.map (MulAut.conj (m : G)).toMonoidHom), a * b = b * a :=
    fun a ha b hb => (hY hb).2 a (hY ha).1
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun y hy => ?_⟩
  refine (Subgroup.iSup_induction _ (C := fun y => y ∈
    (⨆ m : M, X.map (MulAut.conj (m : G)).toMonoidHom) ∧ y ^ 2 = 1) hy
    (fun m x hx => ?_) ⟨one_mem _, one_pow 2⟩ (fun a b ha hb => ?_)).2
  · obtain ⟨x₀, hx₀, rfl⟩ := hx
    refine ⟨mem_iSup_of_mem m ⟨x₀, hx₀, rfl⟩, ?_⟩
    simpa using congrArg (MulAut.conj (m : G)).toMonoidHom (hX.2 x₀ hx₀)
  · have hab : Commute a b := hcomm a ha.1 b hb.1
    exact ⟨mul_mem ha.1 hb.1, by rw [hab.mul_pow, ha.2, hb.2, one_mul]⟩

private theorem exists_conj_mem_of_isSylowOf {p : ℕ} [Fact p.Prime] {M T S : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T M) (hS : IsPGroup p S) (hSM : S ≤ M) :
    ∃ g ∈ M, ∀ s ∈ S, g * s * g⁻¹ ∈ T := by
  obtain ⟨T', rfl⟩ := hT
  obtain ⟨P, hP⟩ := (hS.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M P T'
  refine ⟨g, g.2, fun s hs => ?_⟩
  have h2 : (MulAut.conj g) ⟨s, hSM hs⟩ ∈ ((g • P : Sylow p M) : Subgroup M) := by
    rw [sylow_conjugate_eq_map]
    exact Subgroup.mem_map_of_mem _ (hP hs)
  rw [hg] at h2
  exact ⟨_, h2, rfl⟩

theorem le_centralizer_iSup_conj {M T X R : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hXZ : X ≤ centralizer (T : Set G))
    (hRM : R ≤ M) (hMR : M ≤ normalizer (R : Set G))
    (hR : ∀ r ∈ R, ∃ k : ℕ, r ^ (2 ^ k) ∈
      centralizer ((⨆ m : M, X.map (MulAut.conj (m : G)).toMonoidHom : Subgroup G) : Set G)) :
    R ≤ centralizer ((⨆ m : M, X.map (MulAut.conj (m : G)).toMonoidHom : Subgroup G) : Set G) := by
  set Y : Subgroup G := ⨆ m : M, X.map (MulAut.conj (m : G)).toMonoidHom
  have hXY : ∀ x ∈ X, ∀ m ∈ M, m * x * m⁻¹ ∈ Y := fun x hx m hm =>
    mem_iSup_of_mem (⟨m, hm⟩ : M) ⟨x, hx, rfl⟩
  let N : Subgroup R := (centralizer (Y : Set G)).subgroupOf R
  have hNnormal : N.Normal :=
    ⟨fun n hn g => conj_mem_centralizer (le_normalizer_iSup_conj M X (hRM g.2)) hn⟩
  have hquot : IsPGroup 2 (R ⧸ N) := by
    intro q
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hR r r.2
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  obtain ⟨S'⟩ : Nonempty (Sylow 2 R) := inferInstance
  have hsup : (S' : Subgroup R) ⊔ N = ⊤ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hquot
    have h1 : ((S' : Subgroup R) ⊔ N).index ∣ (S' : Subgroup R).index :=
      index_dvd_of_le le_sup_left
    have h2 : ((S' : Subgroup R) ⊔ N).index ∣ 2 ^ n := by
      rw [← hn, ← Subgroup.index_eq_card]
      exact index_dvd_of_le le_sup_right
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    have h4 : ¬ 2 ∣ ((S' : Subgroup R) ⊔ N).index := fun h => S'.not_dvd_index (h.trans h1)
    rw [hk] at h4
    have hk0 : k = 0 := by
      by_contra hk0
      exact h4 (dvd_pow_self 2 hk0)
    rw [← Subgroup.index_eq_one, hk, hk0, pow_zero]
  have hS2 : IsPGroup 2 ((S' : Subgroup R).map R.subtype) := S'.isPGroup'.map R.subtype
  obtain ⟨g, hgM, hg⟩ := exists_conj_mem_of_isSylowOf hT hS2 ((map_subtype_le _).trans hRM)
  have hRX : ∀ r ∈ R, ∀ x ∈ X, (g⁻¹ * x * g) * r = r * (g⁻¹ * x * g) := by
    have hZ : (S' : Subgroup R) ⊔ N ≤
        (centralizer (X.map (MulAut.conj g⁻¹).toMonoidHom : Set G)).subgroupOf R := by
      refine sup_le (fun s hs => ?_) (fun n hn => ?_)
      · rintro _ ⟨x, hx, rfl⟩
        have h := mem_centralizer_iff.mp (hXZ hx) _ (hg s ⟨s, hs, rfl⟩)
        calc (MulAut.conj g⁻¹).toMonoidHom x * s = g⁻¹ * (x * (g * s * g⁻¹)) * g := by
              simp [mul_assoc]
          _ = g⁻¹ * ((g * s * g⁻¹) * x) * g := by rw [h]
          _ = s * (MulAut.conj g⁻¹).toMonoidHom x := by simp [mul_assoc]
      · refine centralizer_le ?_ hn
        rintro _ ⟨x, hx, rfl⟩
        simpa using hXY x hx g⁻¹ (M.inv_mem hgM)
    intro r hr x hx
    exact hZ (hsup ▸ mem_top (⟨r, hr⟩ : R)) (g⁻¹ * x * g) ⟨x, hx, by simp⟩
  have hRY : Y ≤ centralizer (R : Set G) := by
    refine iSup_le fun m => ?_
    rintro _ ⟨x, hx, rfl⟩ r hr
    have hk : (m * g)⁻¹ * r * (m * g) ∈ R :=
      (mem_normalizer_iff''.mp (hMR (M.mul_mem m.2 hgM)) r).mp hr
    have h := hRX _ hk x hx
    calc r * (MulAut.conj (m : G)).toMonoidHom x
        = (m * g) * (((m * g)⁻¹ * r * (m * g)) * (g⁻¹ * x * g)) * (m * g)⁻¹ := by
          simp [mul_assoc]
      _ = (m * g) * ((g⁻¹ * x * g) * ((m * g)⁻¹ * r * (m * g))) * (m * g)⁻¹ := by rw [h]
      _ = (MulAut.conj (m : G)).toMonoidHom x * r := by simp [mul_assoc]
  exact le_centralizer_iff.mpr hRY

end CFSG.LocalAnalysis.RankThreeUC
