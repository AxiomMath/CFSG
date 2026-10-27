module

public import CFSG.LocalAnalysis.RankThreeUC.GN15Base
public import CFSG.LocalAnalysis.RankThreeUC.GN15Steps
import CFSG.LocalAnalysis.RankThreeUC.GN15Climb
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN CFSG.Quasithin
  CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

private theorem isComponentOf_conjSub {L : Subgroup G} (hL : IsComponentOf L ⊤) (g : G) :
    IsComponentOf (B6.conjSub g L) ⊤ :=
  (CFSG.isComponent_iff_open _).1
    (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g)
      ((CFSG.isComponent_iff_open L).2 hL))

private theorem normal_biSup_of_conj {P : Subgroup G → Prop}
    (hP : ∀ L, P L → ∀ g : G, P (B6.conjSub g L)) :
    (⨆ L ∈ {L : Subgroup G | P L}, L).Normal where
  conj_mem x hx g := by
    have h : B6.conjSub g (⨆ L ∈ {L : Subgroup G | P L}, L) ≤
        ⨆ L ∈ {L : Subgroup G | P L}, L := by
      simp only [OrderIso.map_iSup]
      exact iSup₂_le fun L hL => le_iSup₂_of_le (B6.conjSub g L) (hP L hL g) le_rfl
    refine h (B6.mem_conjSub.2 ?_)
    simpa [mul_assoc] using hx

private def compNormalizer (G : Type*) [Group G] : Subgroup G :=
  ⨅ L ∈ {L : Subgroup G | IsComponentOf L ⊤}, Subgroup.normalizer (L : Set G)

private theorem mem_compNormalizer {k : G} :
    k ∈ compNormalizer G ↔
      ∀ L : Subgroup G, IsComponentOf L ⊤ → k ∈ Subgroup.normalizer (L : Set G) := by
  simp [compNormalizer, Subgroup.mem_iInf]

private theorem normal_compNormalizer : (compNormalizer G).Normal where
  conj_mem k hk g := by
    rw [mem_compNormalizer] at hk ⊢
    intro L hL
    have h1 := hk _ (isComponentOf_conjSub hL g⁻¹)
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro x
    have h2 := h1 (g⁻¹ * x * g)
    simp only [B6.mem_conjSub, inv_inv] at h2
    convert h2 using 2 <;> group

private theorem conjSub_commutator (g : G) (H K : Subgroup G) :
    B6.conjSub g ⁅H, K⁆ = ⁅B6.conjSub g H, B6.conjSub g K⁆ :=
  Subgroup.map_commutator H K (MulAut.conj g).toMonoidHom

private theorem normal_rankThreeLayer_top : (rankThreeLayer (⊤ : Subgroup G)).Normal := by
  unfold rankThreeLayer
  rw [sSup_eq_iSup]
  exact normal_biSup_of_conj (P := fun L => IsComponentOf L ⊤)
    (fun _ hL g => isComponentOf_conjSub hL g)

end Generic

section Invariance

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

private theorem exists_normalizer_conj_eq (hX : GNSetting X T) (x : X) :
    ∃ n ∈ Subgroup.normalizer (thompsonJ T : Set X),
      ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ →
        B6.conjSub (toStar T x) L = B6.conjSub (toStar T n) L := by
  set W : Subgroup X := (compNormalizer (X ⧸ gnC T)).comap (toStar T) with hWdef
  have hW : W.Normal := (normal_compNormalizer).comap _
  have hJ : thompsonJ T ≤ W := fun j hj => by
    rw [hWdef, Subgroup.mem_comap, mem_compNormalizer]
    intro L hL
    exact thompsonJ_le_normalizer_of_isComponentOf hX hL ⟨j, hj, rfl⟩
  obtain ⟨w, hw, n, hn, rfl⟩ := frattini_of_normal_thompsonJ_le hX hW hJ x
  refine ⟨n, hn, fun L hL => ?_⟩
  rw [map_mul, B6.conjSub_mul]
  exact B6.conjSub_eq_self ((mem_compNormalizer.1 (Subgroup.mem_comap.1 hw)) _
    (isComponentOf_conjSub hL _))

private theorem conj_mem_commutator_ne_bot (hX : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤ ∧ ⁅L, gnImg T (thompsonJ T)⁆ ≠ ⊥) (g : X ⧸ gnC T) :
    IsComponentOf (B6.conjSub g L) ⊤ ∧ ⁅B6.conjSub g L, gnImg T (thompsonJ T)⁆ ≠ ⊥ := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨n, hn, hconj⟩ := exists_normalizer_conj_eq hX x
  have hx : B6.conjSub (↑x : X ⧸ gnC T) L = B6.conjSub (toStar T n) L := hconj L hL.1
  rw [hx]
  refine ⟨isComponentOf_conjSub hL.1 _, fun hbot => hL.2 ?_⟩
  have hnJ : toStar T n ∈ Subgroup.normalizer (gnImg T (thompsonJ T) : Set (X ⧸ gnC T)) :=
    Subgroup.le_normalizer_map _ ⟨n, hn, rfl⟩
  have hJ : B6.conjSub (toStar T n) (gnImg T (thompsonJ T)) = gnImg T (thompsonJ T) :=
    B6.conjSub_eq_self hnJ
  have h2 : ⁅B6.conjSub (toStar T n) L, gnImg T (thompsonJ T)⁆ =
      B6.conjSub (toStar T n) ⁅L, gnImg T (thompsonJ T)⁆ := by
    conv_lhs => rw [← hJ]
    exact (conjSub_commutator _ _ _).symm
  rw [h2] at hbot
  exact (B6.conjSub (toStar T n)).injective (by rw [hbot, OrderIso.map_bot])

theorem gnDStar_normal (hX : GNSetting X T) : (gnDStar T).Normal :=
  normal_biSup_of_conj
    (P := fun L => IsComponentOf L ⊤ ∧ ⁅L, gnImg T (thompsonJ T)⁆ ≠ ⊥)
    (fun _ hL g => conj_mem_commutator_ne_bot hX hL g)

theorem gnDPre_normal (hX : GNSetting X T) : (gnDPre T).Normal :=
  (gnDStar_normal hX).comap _

theorem gnQPre_normal (hX : GNSetting X T) : (gnQPre T).Normal := by
  have := gnDStar_normal hX
  exact Subgroup.Normal.comap (Subgroup.normal_centralizer) _

end Invariance

section Layer

variable {X : Type} [Group X] {T : Subgroup X}

theorem gnHPre_normal : (gnHPre T).Normal := by
  have : (rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T))).Normal := normal_rankThreeLayer_top
  exact Subgroup.Normal.comap (Subgroup.normal_centralizer) _

private theorem gnDStar_le_layer : gnDStar T ≤ rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T)) :=
  iSup₂_le fun _ hL => le_sSup hL.1

theorem gnHPre_le_gnQPre : gnHPre T ≤ gnQPre T :=
  Subgroup.comap_mono (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 gnDStar_le_layer))

end Layer

section Commutator

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

private theorem commutator_mem_centralizer_component (hX : GNSetting X T)
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤) {q j : X ⧸ gnC T}
    (hq : q ∈ Subgroup.centralizer (gnDStar T : Set (X ⧸ gnC T)))
    (hj : j ∈ gnImg T (thompsonJ T)) :
    ⁅q, j⁆ ∈ Subgroup.centralizer (L : Set (X ⧸ gnC T)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  by_cases hS : ⁅L, gnImg T (thompsonJ T)⁆ = ⊥
  ·
    have hJC : ∀ y : X ⧸ gnC T, y ∈ L → j * y = y * j := fun y hy =>
      Subgroup.mem_centralizer_iff.1
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hS hy) j hj
    set L' : Subgroup (X ⧸ gnC T) := B6.conjSub q⁻¹ L with hL'
    have hL'S : ⁅L', gnImg T (thompsonJ T)⁆ = ⊥ := by
      by_contra hne
      have h1 := conj_mem_commutator_ne_bot hX ⟨isComponentOf_conjSub hL _, hne⟩ q
      have h2 : B6.conjSub q L' = L := by
        rw [hL', ← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one]
      rw [h2] at h1
      exact h1.2 hS
    have hmem : q⁻¹ * l * q ∈ L' := by
      rw [hL', B6.mem_conjSub]
      have : (q⁻¹)⁻¹ * (q⁻¹ * l * q) * q⁻¹ = l := by group
      rw [this]
      exact hl
    have h3 : j * (q⁻¹ * l * q) = (q⁻¹ * l * q) * j :=
      Subgroup.mem_centralizer_iff.1
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hL'S hmem) j hj
    have h4 : j * l = l * j := hJC l hl
    have h5 : l * j⁻¹ = j⁻¹ * l := by
      calc l * j⁻¹ = j⁻¹ * (j * l) * j⁻¹ := by group
        _ = j⁻¹ * (l * j) * j⁻¹ := by rw [h4]
        _ = j⁻¹ * l := by group
    calc l * ⁅q, j⁆ = q * ((q⁻¹ * l * q) * j) * q⁻¹ * j⁻¹ := by
          rw [commutatorElement_def]; group
      _ = q * (j * (q⁻¹ * l * q)) * q⁻¹ * j⁻¹ := by rw [← h3]
      _ = q * j * q⁻¹ * (l * j⁻¹) := by group
      _ = ⁅q, j⁆ * l := by rw [h5, commutatorElement_def]; group
  ·
    have hLD : L ≤ gnDStar T := le_iSup₂_of_le L ⟨hL, hS⟩ le_rfl
    have hqL : ∀ y ∈ L, y * q = q * y := fun y hy =>
      Subgroup.mem_centralizer_iff.1 hq y (hLD hy)
    have hjN : j ∈ Subgroup.normalizer (L : Set (X ⧸ gnC T)) :=
      thompsonJ_le_normalizer_of_isComponentOf hX hL hj
    have hl' : j⁻¹ * l * j ∈ L := (Subgroup.mem_normalizer_iff''.1 hjN l).1 hl
    have hc0 : l * q = q * l := hqL l hl
    have hc1 : (j⁻¹ * l * j) * q⁻¹ = q⁻¹ * (j⁻¹ * l * j) :=
      Commute.inv_right (show Commute (j⁻¹ * l * j) q from hqL _ hl')
    calc l * ⁅q, j⁆ = (l * q) * j * q⁻¹ * j⁻¹ := by rw [commutatorElement_def]; group
      _ = q * j * ((j⁻¹ * l * j) * q⁻¹) * j⁻¹ := by rw [hc0]; group
      _ = q * j * (q⁻¹ * (j⁻¹ * l * j)) * j⁻¹ := by rw [hc1]
      _ = ⁅q, j⁆ * l := by rw [commutatorElement_def]; group

theorem commutator_gnQPre_le_gnHPre (hX : GNSetting X T) :
    ⁅gnQPre T, thompsonJ T⁆ ≤ gnHPre T := by
  rw [Subgroup.commutator_le]
  intro q hq j hj
  have hq' : toStar T q ∈ Subgroup.centralizer (gnDStar T : Set (X ⧸ gnC T)) :=
    Subgroup.mem_comap.1 hq
  have hj' : toStar T j ∈ gnImg T (thompsonJ T) := ⟨j, hj, rfl⟩
  refine Subgroup.mem_comap.2 ?_
  rw [map_commutatorElement]
  have hle : rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T)) ≤
      Subgroup.centralizer {⁅toStar T q, toStar T j⁆} := by
    refine sSup_le fun L hL => ?_
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1
      (commutator_mem_centralizer_component hX hL hq' hj') l hl)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem gnQPre_le_sup_normalizer (hX : GNSetting X T) :
    gnQPre T ≤ gnHPre T ⊔ Subgroup.normalizer (thompsonJ T : Set X) := by
  intro q hq
  obtain ⟨b, hb, n, hn, rfl⟩ := eq_mul_normalizer_thompsonJ_of_commutator_le hX.sylow
    gnHPre_normal gnHPre_le_gnQPre (commutator_gnQPre_le_gnHPre hX) q hq
  exact Subgroup.mul_mem_sup hb hn.2

end Commutator

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
