module

public import CFSG.CGT.Foote82.BlockBasics
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCFooteBlocks
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTI

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem le_normalizer_commutator {X A B : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hx),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hx)]

private theorem commutator_eq_bot_of_perfect {X A : Subgroup G} (hA : ⁅A, A⁆ = A)
    (h : ⁅⁅X, A⁆, A⁆ = ⊥) : ⁅X, A⁆ = ⊥ := by
  have h1 : ⁅⁅A, X⁆, A⁆ = ⊥ := by rw [Subgroup.commutator_comm A X]; exact h
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h
  rw [hA] at h3
  rw [Subgroup.commutator_comm]
  exact h3

private theorem commutator_commutator_le_of_rotate {N H₁ H₂ H₃ : Subgroup G}
    (h₁ : H₁ ≤ Subgroup.normalizer (N : Set G)) (h₂ : H₂ ≤ Subgroup.normalizer (N : Set G))
    (h₃ : H₃ ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N)
    (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) : ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  set K := Subgroup.normalizer (N : Set G) with hK
  set f : ↥K →* ↥K ⧸ N.subgroupOf K := QuotientGroup.mk' (N.subgroupOf K) with hf
  have hmap : ∀ {H : Subgroup G}, H ≤ K → (H.subgroupOf K).map K.subtype = H := fun hH => by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hH]
  have key : ∀ X : Subgroup ↥K, X.map K.subtype ≤ N ↔ X.map f = ⊥ := by
    intro X
    rw [Subgroup.map_eq_bot_iff, hf, QuotientGroup.ker_mk', Subgroup.map_le_iff_le_comap]
    rfl
  have e : ∀ {H H' H'' : Subgroup G}, H ≤ K → H' ≤ K → H'' ≤ K →
      ⁅⁅H, H'⁆, H''⁆ =
        (⁅⁅H.subgroupOf K, H'.subgroupOf K⁆, H''.subgroupOf K⁆).map K.subtype := by
    intro H H' H'' hH hH' hH''
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hmap hH, hmap hH', hmap hH'']
  rw [e h₂ h₃ h₁, key, Subgroup.map_commutator, Subgroup.map_commutator] at h1
  rw [e h₃ h₁ h₂, key, Subgroup.map_commutator, Subgroup.map_commutator] at h2
  rw [e h₁ h₂ h₃, key, Subgroup.map_commutator, Subgroup.map_commutator]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

private theorem inf_centralizer_ne_bot {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQ0 : Q ≠ ⊥) :
    Q ⊓ Subgroup.centralizer (Q : Set G) ≠ ⊥ := by
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ0
  have : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
  obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center Q)
  intro hbot
  have hzmem : (z : G) ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
    refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    have := Subgroup.mem_center_iff.mp hz ⟨h, hh⟩
    exact congrArg Subtype.val this
  rw [hbot, Subgroup.mem_bot] at hzmem
  apply hz1
  exact Subtype.ext (Subtype.ext hzmem)

private theorem le_normalizer_inf_centralizer {X Q : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (Q : Set G)) :
    X ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) := by
  intro x hx
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  have hn' : n ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := hn
  have hxQ : ∀ q, q ∈ Q ↔ x * q * x⁻¹ ∈ Q := Subgroup.mem_normalizer_iff.mp (hX hx)
  show x * n * x⁻¹ ∈ Q ⊓ Subgroup.centralizer (Q : Set G)
  refine ⟨(hxQ n).mp hn'.1, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
  have hq' : x⁻¹ * q * x ∈ Q := by
    refine (hxQ (x⁻¹ * q * x)).mpr ?_
    have e : x * (x⁻¹ * q * x) * x⁻¹ = q := by group
    rw [e]
    exact hq
  have hc := Subgroup.mem_centralizer_iff.mp hn'.2 _ hq'
  calc q * (x * n * x⁻¹) = x * ((x⁻¹ * q * x) * n) * x⁻¹ := by group
    _ = x * (n * (x⁻¹ * q * x)) * x⁻¹ := by rw [hc]
    _ = x * n * x⁻¹ * q := by group

private theorem pCoreOf_le_pCoreOf_of_subnormal {H K : Subgroup G} (h : IsSubnormal H K) :
    pCoreOf 2 H ≤ pCoreOf 2 K := by
  induction h with
  | refl => exact le_rfl
  | @step H M K hle hN _ ih =>
    refine le_trans ?_ ih
    refine le_pCoreOf_of_le_normalizer
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H).trans hle) ?_
      (CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.isPGroup_pCoreOf H)
    intro m hm
    have hmH : m ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN hm
    exact CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.normalizer_le_normalizer_pCoreOf H hmH

private theorem pCoreOf_ne_bot_of_max {M : Subgroup G} (hM : GLBIsMaxTwoLocal M) :
    pCoreOf 2 M ≠ ⊥ := by
  obtain ⟨P, hP0, hP2, hMP⟩ := hM.1
  intro h
  apply hP0
  have hPM : P ≤ M := hMP ▸ Subgroup.le_normalizer
  have : P ≤ pCoreOf 2 M := le_pCoreOf_of_le_normalizer hPM hMP.le hP2
  rw [h] at this
  exact le_bot_iff.mp this

private theorem normalizer_eq_of_max {M Y : Subgroup G} (hM : GLBIsMaxTwoLocal M)
    (hY : Y ≤ pCoreOf 2 M) (hY0 : Y ≠ ⊥) (hMY : M ≤ Subgroup.normalizer (Y : Set G)) :
    Subgroup.normalizer (Y : Set G) = M :=
  hM.2 _ ⟨Y, hY0, (CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.isPGroup_pCoreOf M).to_le hY, rfl⟩ hMY

private theorem mem_centralizerModTwoCore {J : Subgroup G} {x : G}
    (hx : x ∈ centralizerModTwoCore J) :
    x ∈ Subgroup.normalizer (J : Set G) ∧ ∀ y ∈ J, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 J := by
  have hN := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.normalizer_le_normalizer_pCoreOf J
  have hx' : x ∈ Subgroup.closure {g : G | g ∈ Subgroup.normalizer (J : Set G) ∧
      ∀ y ∈ J, g * y * g⁻¹ * y⁻¹ ∈ pCoreOf 2 J} := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem g hg => exact hg
  | one => exact ⟨one_mem _, fun y _ => by simpa using (pCoreOf 2 J).one_mem⟩
  | mul a b _ _ iha ihb =>
    refine ⟨mul_mem iha.1 ihb.1, fun y hy => ?_⟩
    have e : a * b * y * (a * b)⁻¹ * y⁻¹ =
        a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ * (a * y * a⁻¹ * y⁻¹) := by group
    rw [e]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hN iha.1) _).mp (ihb.2 y hy)) (iha.2 y hy)
  | inv a _ iha =>
    refine ⟨inv_mem iha.1, fun y hy => ?_⟩
    have hy' : a⁻¹ * y * a ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem iha.1) y).mp hy
      simpa using this
    have h := iha.2 _ hy'
    have e : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = (a * (a⁻¹ * y * a) * a⁻¹ * (a⁻¹ * y * a)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h

private theorem commutator_blockU_eq_bot {H J R : Subgroup G} (hJ : IsFooteBlock H J)
    (hR : IsPGroup 2 R) (hRJ : R ≤ Subgroup.normalizer (J : Set G)) (hc : ⁅R, J⁆ ≤ blockQ J)
    (hU : ∀ u ∈ blockU J, ∀ v ∈ blockU J, u * v = v * u) : ⁅blockU J, R⁆ = ⊥ := by
  have hZJ : blockZ J ≤ Subgroup.centralizer (J : Set G) := inf_le_right
  have hUU : ⁅blockU J, blockU J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hU y hy x hx
  have h1 : ⁅⁅J, R⁆, blockU J⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono (IsFooteBlock.commutator_le_blockU hJ hRJ hc)
      le_rfl).trans hUU.le)
  have h2 : ⁅⁅R, blockU J⁆, J⁆ = ⊥ := by
    refine le_bot_iff.mp ((Subgroup.commutator_mono ?_ le_rfl).trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZJ).le)
    rw [Subgroup.commutator_comm]
    exact IsFooteBlock.commutator_blockU_le_blockZ hJ hR hRJ hc
  have h3 : ⁅⁅blockU J, J⁆, R⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [IsFooteBlock.commutator_blockU hJ] at h3

private theorem commutator_commutator_eq_bot_of_not_abelian {H J R : Subgroup G}
    (hJ : IsFooteBlock H J) (hR : IsPGroup 2 R) (hRJ : R ≤ Subgroup.normalizer (J : Set G))
    (hc : ⁅R, J⁆ ≤ blockQ J)
    (hU : ¬ ∀ u ∈ blockU J, ∀ v ∈ blockU J, u * v = v * u) : ⁅⁅R, R⁆, J⁆ = ⊥ := by
  have hZJ : blockZ J ≤ Subgroup.centralizer (J : Set G) := inf_le_right
  have hUJ : blockU J ≤ J := blockU_le_self J
  have hZC : blockZ J ≤ Subgroup.centralizer (blockU J : Set G) :=
    hZJ.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUJ))
  have hURZ : ⁅blockU J, R⁆ ≤ blockZ J := IsFooteBlock.commutator_blockU_le_blockZ hJ hR hRJ hc
  have hRUZ : ⁅R, blockU J⁆ ≤ blockZ J := by rw [Subgroup.commutator_comm]; exact hURZ
  have hJRU : ⁅J, R⁆ ≤ blockU J := IsFooteBlock.commutator_le_blockU hJ hRJ hc
  have hZJbot : ⁅blockZ J, J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZJ
  have hZUbot : ⁅blockZ J, blockU J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZC
  have hJQ : J ≤ Subgroup.normalizer (blockQ J : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J
  have hRQ : R ≤ Subgroup.normalizer (blockQ J : Set G) :=
    hRJ.trans (CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.normalizer_le_normalizer_pCoreOf J)
  have hRU : R ≤ Subgroup.normalizer (blockU J : Set G) := le_normalizer_commutator hRQ hRJ
  have hJU : J ≤ Subgroup.normalizer (blockU J : Set G) :=
    le_normalizer_commutator hJQ Subgroup.le_normalizer
  have hUU : blockU J ≤ Subgroup.normalizer ((⁅blockU J, blockU J⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left _ _
  have hRU' := le_normalizer_commutator hRU hRU
  have hJU' := le_normalizer_commutator hJU hJU
  have h1 : ⁅blockU J, R⁆ ≤ ⁅blockU J, blockU J⁆ := by
    have := commutator_commutator_le_of_rotate (N := ⁅blockU J, blockU J⁆) (H₁ := blockU J)
      (H₂ := J) (H₃ := R) hUU hJU' hRU'
      ((Subgroup.commutator_mono hJRU le_rfl))
      ((Subgroup.commutator_mono hRUZ le_rfl).trans (hZJbot.le.trans bot_le))
    rwa [IsFooteBlock.commutator_blockU hJ] at this
  have h2 : ⁅⁅blockU J, blockU J⁆, R⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := blockU J) (H₂ := blockU J)
      (H₃ := R) ?_ ?_
    · exact le_bot_iff.mp ((Subgroup.commutator_mono hURZ le_rfl).trans hZUbot.le)
    · exact le_bot_iff.mp ((Subgroup.commutator_mono hRUZ le_rfl).trans hZUbot.le)
  have h3 : ⁅⁅blockU J, R⁆, R⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono h1 le_rfl).trans h2.le)
  have h4 : ⁅⁅R, R⁆, blockU J⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := R) (H₂ := R)
      (H₃ := blockU J) ?_ h3
    rw [Subgroup.commutator_comm R (blockU J)]
    exact h3
  have h5 : ⁅R, R⁆ ≤ Subgroup.centralizer (blockU J : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h4
  have h6 : ⁅J, ⁅R, R⁆⁆ ≤ Subgroup.centralizer (blockU J : Set G) := by
    rw [Subgroup.commutator_le]
    intro x hx r hr
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : x⁻¹ * u * x ∈ blockU J := by
      have := (Subgroup.mem_normalizer_iff.mp (hJU (J.inv_mem hx)) u).mp hu
      simpa using this
    have hr1 : Commute u r := Subgroup.mem_centralizer_iff.mp (h5 hr) u hu
    have hr2 : Commute (x⁻¹ * u * x) r := Subgroup.mem_centralizer_iff.mp (h5 hr) _ hu'
    have h7 : Commute u (x * r * x⁻¹) := by
      unfold Commute SemiconjBy
      calc u * (x * r * x⁻¹) = x * ((x⁻¹ * u * x) * r) * x⁻¹ := by group
        _ = x * (r * (x⁻¹ * u * x)) * x⁻¹ := by rw [hr2.eq]
        _ = x * r * x⁻¹ * u := by group
    have h8 : Commute u ((x * r * x⁻¹) * r⁻¹) := h7.mul_right hr1.inv_right
    have e : ⁅x, r⁆ = (x * r * x⁻¹) * r⁻¹ := rfl
    rw [e]
    exact h8.eq
  have h9 : ⁅J, ⁅R, R⁆⁆ ≤ J ⊓ Subgroup.centralizer (blockU J : Set G) := by
    refine le_inf ?_ h6
    exact (Subgroup.commutator_mono le_rfl (Subgroup.commutator_le_of_le le_rfl le_rfl)).trans
      (hJRU.trans hUJ)
  have h10 : ⁅⁅J, ⁅R, R⁆⁆, J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (h9.trans (IsFooteBlock.inf_centralizer_blockU_le hJ hU))
  have h11 : ⁅⁅⁅R, R⁆, J⁆, J⁆ = ⊥ := by
    rw [Subgroup.commutator_comm ⁅R, R⁆ J]
    exact h10
  exact commutator_eq_bot_of_perfect (IsFooteBlock.commutator_eq hJ) h11

private theorem forall_conj_mem_of_abelian (hc : IsCharTwoType G) {M J M₁ R : Subgroup G}
    (hJ : IsFooteBlock M J) (hM₁ : GLBIsMaxTwoLocal M₁) (hR : IsPGroup 2 R)
    (hRJ : R ≤ Subgroup.normalizer (J : Set G)) (hRc : ⁅R, J⁆ ≤ blockQ J)
    (hQ₁R : pCoreOf 2 M₁ ≤ R) (hQQ₁ : blockQ J ≤ pCoreOf 2 M₁)
    (hU : ∀ u ∈ blockU J, ∀ v ∈ blockU J, u * v = v * u) :
    ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ j ∈ J, g⁻¹ * j * g ∈ M₁ := by
  have hQ₁2 : IsPGroup 2 (pCoreOf 2 M₁) :=
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.isPGroup_pCoreOf M₁
  set Y : Subgroup G := pCoreOf 2 M₁ ⊓ Subgroup.centralizer (pCoreOf 2 M₁ : Set G) with hY
  have hYne : Y ≠ ⊥ := inf_centralizer_ne_bot hQ₁2 (pCoreOf_ne_bot_of_max hM₁)
  have hM₁Y : M₁ ≤ Subgroup.normalizer (Y : Set G) :=
    le_normalizer_inf_centralizer
      (CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.le_normalizer_pCoreOf M₁)
  have hNY : Subgroup.normalizer (Y : Set G) = M₁ :=
    normalizer_eq_of_max hM₁ inf_le_left hYne hM₁Y
  have hUQ : blockU J ≤ blockQ J := Subgroup.le_normalizer_iff_commutator_le_left.mp
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J)
  have hUR : blockU J ≤ R := hUQ.trans (hQQ₁.trans hQ₁R)
  have hURc : ∀ u ∈ blockU J, ∀ r ∈ R, r * u = u * r := by
    have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (commutator_blockU_eq_bot hJ hR hRJ hRc hU)
    intro u hu r hr
    exact Subgroup.mem_centralizer_iff.mp (h hu) r hr
  have hZRY : ∀ x ∈ R, (∀ r ∈ R, r * x = x * r) → x ∈ Y := by
    intro x hxR hxc
    have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 M₁ : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun h hh => hxc h (hQ₁R hh)
    have hxM₁ : x ∈ M₁ := by
      rw [← hNY]
      apply Subgroup.mem_normalizer_fintype
      intro n hn
      have hnx : n * x = x * n := hxc n (hQ₁R (inf_le_left (a := pCoreOf 2 M₁) hn))
      show x * n * x⁻¹ ∈ Y
      rw [← hnx, mul_inv_cancel_right]
      exact hn
    exact ⟨hc M₁ hM₁.1 ⟨hxM₁, hxC⟩, hxC⟩
  intro g hg j hj
  rw [← hNY]
  apply Subgroup.mem_normalizer_fintype
  intro y hy
  have hyY : y ∈ Y := hy
  have hwR : g * y * g⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp hg y).mp (hQ₁R (inf_le_left (a := pCoreOf 2 M₁) hyY))
  have hz : ⁅j, g * y * g⁻¹⁆ ∈ blockU J := IsFooteBlock.commutator_le_blockU hJ hRJ hRc
    (Subgroup.commutator_mem_commutator hj hwR)
  obtain ⟨z, hzdef⟩ : ∃ z, z = ⁅j, g * y * g⁻¹⁆ := ⟨_, rfl⟩
  rw [← hzdef] at hz
  have hzR : g⁻¹ * z * g ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) z).mp (hUR hz)
    simpa using this
  have hzc : ∀ r ∈ R, r * (g⁻¹ * z * g) = (g⁻¹ * z * g) * r := by
    intro r hr
    have hr' : g * r * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hg r).mp hr
    have h := hURc z hz _ hr'
    calc r * (g⁻¹ * z * g) = g⁻¹ * ((g * r * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * r * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * z * g) * r := by group
  have hmem : g⁻¹ * z * g ∈ Y := hZRY _ hzR hzc
  have e : g⁻¹ * j * g * y * (g⁻¹ * j * g)⁻¹ = (g⁻¹ * z * g) * y := by
    rw [hzdef, commutatorElement_def]
    group
  show g⁻¹ * j * g * y * (g⁻¹ * j * g)⁻¹ ∈ Y
  rw [e]
  exact Y.mul_mem hmem hyY

private theorem forall_conj_mem_of_not_abelian {M J M₁ R : Subgroup G}
    (hJ : IsFooteBlock M J) (hM₁ : GLBIsMaxTwoLocal M₁) (hR : IsPGroup 2 R)
    (hRJ : R ≤ Subgroup.normalizer (J : Set G)) (hRc : ⁅R, J⁆ ≤ blockQ J)
    (hQ₁R : pCoreOf 2 M₁ ≤ R) (hQQ₁ : blockQ J ≤ pCoreOf 2 M₁)
    (hU : ¬ ∀ u ∈ blockU J, ∀ v ∈ blockU J, u * v = v * u) :
    ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ j ∈ J, g⁻¹ * j * g ∈ M₁ := by
  have hQ₁N : M₁ ≤ Subgroup.normalizer (pCoreOf 2 M₁ : Set G) :=
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.le_normalizer_pCoreOf M₁
  have hUQ : blockU J ≤ blockQ J := Subgroup.le_normalizer_iff_commutator_le_left.mp
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J)
  have hYne : ⁅pCoreOf 2 M₁, pCoreOf 2 M₁⁆ ≠ ⊥ := by
    intro h
    apply hU
    intro u hu v hv
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact (Subgroup.mem_centralizer_iff.mp (h1 (hQQ₁ (hUQ hu))) v (hQQ₁ (hUQ hv))).symm
  have hM₁Y : M₁ ≤ Subgroup.normalizer ((⁅pCoreOf 2 M₁, pCoreOf 2 M₁⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hQ₁N hQ₁N
  have hNY : Subgroup.normalizer ((⁅pCoreOf 2 M₁, pCoreOf 2 M₁⁆ : Subgroup G) : Set G) = M₁ :=
    normalizer_eq_of_max hM₁ (Subgroup.commutator_le_of_le le_rfl le_rfl) hYne hM₁Y
  have hR'J : ⁅R, R⁆ ≤ Subgroup.centralizer (J : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (commutator_commutator_eq_bot_of_not_abelian hJ hR hRJ hRc hU)
  intro g hg j hj
  rw [← hNY]
  apply Subgroup.mem_normalizer_fintype
  intro y hy
  have hgR' : g ∈ Subgroup.normalizer ((⁅R, R⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator (X := Subgroup.normalizer (R : Set G)) le_rfl le_rfl hg
  have hw : g * y * g⁻¹ ∈ ⁅R, R⁆ :=
    (Subgroup.mem_normalizer_iff.mp hgR' y).mp (Subgroup.commutator_mono hQ₁R hQ₁R hy)
  have hwj : j * (g * y * g⁻¹) = (g * y * g⁻¹) * j :=
    Subgroup.mem_centralizer_iff.mp (hR'J hw) j hj
  have e : g⁻¹ * j * g * y * (g⁻¹ * j * g)⁻¹ = y := by
    calc g⁻¹ * j * g * y * (g⁻¹ * j * g)⁻¹ = g⁻¹ * (j * (g * y * g⁻¹)) * j⁻¹ * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * j) * j⁻¹ * g := by rw [hwj]
      _ = y := by group
  show g⁻¹ * j * g * y * (g⁻¹ * j * g)⁻¹ ∈ ⁅pCoreOf 2 M₁, pCoreOf 2 M₁⁆
  rw [e]
  exact hy

private theorem isFooteBlock_normalizer_of_forall_conj_mem {M J M₁ R : Subgroup G}
    (hJ : IsFooteBlock M J) (hsub : IsSubnormal J M₁)
    (hJR : J ≤ Subgroup.normalizer (R : Set G))
    (hmain : ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ j ∈ J, g⁻¹ * j * g ∈ M₁) :
    IsFooteBlock (Subgroup.normalizer (R : Set G)) J := by
  set N := Subgroup.normalizer (R : Set G) with hN
  let D : Subgroup G :=
    { carrier := {x | x ∈ N ∧ ∀ g ∈ N, g * x * g⁻¹ ∈ M₁}
      mul_mem' := fun {a b} ha hb => ⟨N.mul_mem ha.1 hb.1, fun g hg => by
        have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [e]
        exact M₁.mul_mem (ha.2 g hg) (hb.2 g hg)⟩
      one_mem' := ⟨N.one_mem, fun g _ => by simpa using M₁.one_mem⟩
      inv_mem' := fun {a} ha => ⟨N.inv_mem ha.1, fun g hg => by
        have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [e]
        exact M₁.inv_mem (ha.2 g hg)⟩ }
  have hDN : D ≤ N := fun x hx => hx.1
  have hDM₁ : D ≤ M₁ := fun x hx => by simpa using hx.2 1 N.one_mem
  have hJD : J ≤ D := fun j hj => ⟨hJR hj, fun g hg => by
    simpa using hmain g⁻¹ (N.inv_mem hg) j hj⟩
  have hDnormal : (D.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hDN]
    intro h n hh hn
    refine ⟨N.mul_mem (N.mul_mem hn (hDN hh)) (N.inv_mem hn), fun g hg => ?_⟩
    have := hh.2 (g * n) (N.mul_mem hg hn)
    have e : g * (n * h * n⁻¹) * g⁻¹ = g * n * h * (g * n)⁻¹ := by group
    rw [e]
    exact this
  have hJDsub : IsSubnormal J D := by
    have := hsub.inf_of_le hDM₁
    rwa [inf_eq_left.mpr hJD] at this
  exact ⟨hJR, hJDsub.trans (.step hDN hDnormal (.refl N)), hJ.residual, hJ.quasisimple, hJ.chief⟩

theorem footeSix_of_D1 (hc : IsCharTwoType G) {M J : Subgroup G} (hJ : IsFooteBlock M J)
    (hD1 : ∃ M₁ : Subgroup G, GLBIsMaxTwoLocal M₁ ∧ Subgroup.normalizer (J : Set G) ≤ M₁ ∧
      IsSubnormal J M₁) : InFooteB J := by
  obtain ⟨M₁, hM₁, hNM₁, hsub⟩ := hD1
  have hQ₁2 : IsPGroup 2 (pCoreOf 2 M₁) :=
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.isPGroup_pCoreOf M₁
  have hQ₁N : M₁ ≤ Subgroup.normalizer (pCoreOf 2 M₁ : Set G) :=
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.le_normalizer_pCoreOf M₁
  have hQ₁M : pCoreOf 2 M₁ ≤ M₁ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M₁
  have hQQ₁ : blockQ J ≤ pCoreOf 2 M₁ := pCoreOf_le_pCoreOf_of_subnormal hsub
  obtain ⟨R, hRsyl, -⟩ := EscapingLocal.exists_isSylowTwoOf_ge (H := centralizerModTwoCore J)
    (P := ⊥) bot_le (by simp [IsPGroup])
  have hRC : R ≤ centralizerModTwoCore J := hRsyl.1
  have hR2 : IsPGroup 2 R := hRsyl.2.1
  have hCN : centralizerModTwoCore J ≤ Subgroup.normalizer (J : Set G) :=
    Subgroup.closure_le _ |>.mpr fun g hg => hg.1
  have hRJ : R ≤ Subgroup.normalizer (J : Set G) := hRC.trans hCN
  have hRc : ⁅R, J⁆ ≤ blockQ J := by
    rw [Subgroup.commutator_le]
    intro r hr x hx
    exact (mem_centralizerModTwoCore (hRC hr)).2 x hx
  have hQ₁N' : pCoreOf 2 M₁ ≤ Subgroup.normalizer (J : Set G) :=
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.le_normalizer_of_isSubnormal_of_twoResidual
      hsub hJ.residual hQ₁2 hQ₁M hQ₁N
  have hQ₁JQ : pCoreOf 2 M₁ ⊓ J ≤ pCoreOf 2 J := by
    refine le_pCoreOf_of_le_normalizer inf_le_right ?_ (hQ₁2.to_le inf_le_left)
    intro j hj
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hQ₁N (hsub.le hj), Subgroup.le_normalizer hj⟩
  have hQ₁C : pCoreOf 2 M₁ ≤ centralizerModTwoCore J := by
    intro q hq
    refine Subgroup.subset_closure ⟨hQ₁N' hq, fun x hx => ?_⟩
    have h1 : q * x * q⁻¹ * x⁻¹ ∈ pCoreOf 2 M₁ := by
      have h := (Subgroup.mem_normalizer_iff.mp (hQ₁N (hsub.le hx)) q⁻¹).mp (inv_mem hq)
      have e : q * x * q⁻¹ * x⁻¹ = q * (x * q⁻¹ * x⁻¹) := by group
      rw [e]
      exact mul_mem hq h
    have h2 : q * x * q⁻¹ * x⁻¹ ∈ J :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (hQ₁N' hq) x).mp hx) (inv_mem hx)
    exact hQ₁JQ ⟨h1, h2⟩
  have hCQ₁ : centralizerModTwoCore J ≤ Subgroup.normalizer (pCoreOf 2 M₁ : Set G) :=
    hCN.trans (hNM₁.trans hQ₁N)
  have hQ₁R : pCoreOf 2 M₁ ≤ R :=
    (le_pCoreOf_of_le_normalizer hQ₁C hCQ₁ hQ₁2).trans
      (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hRsyl)
  have hJR : J ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hRc.trans (hQQ₁.trans hQ₁R))
  refine ⟨R, hRsyl, isFooteBlock_normalizer_of_forall_conj_mem hJ hsub hJR ?_⟩
  by_cases hU : ∀ u ∈ blockU J, ∀ v ∈ blockU J, u * v = v * u
  · exact forall_conj_mem_of_abelian hc hJ hM₁ hR2 hRJ hRc hQ₁R hQQ₁ hU
  · exact forall_conj_mem_of_not_abelian hJ hM₁ hR2 hRJ hRc hQ₁R hQQ₁ hU

end CFSG.CGT.Foote82
