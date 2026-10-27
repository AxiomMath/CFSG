module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Matrix CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding

theorem eq_succ_of_dvd_sq_sub_one {p n : ℕ} (hp : p.Prime) (hdvd : n ∣ p ^ 2 - 1)
    (hmod : n ≡ 1 [MOD p]) (hn1 : n ≠ 1) : n = p + 1 := by
  have hp2 := hp.two_le
  have hp4 : 4 ≤ p ^ 2 := by nlinarith
  obtain ⟨m, hm⟩ := hdvd
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
  have hpn : p ∣ n - 1 := (Nat.modEq_iff_dvd' hn0).mp hmod.symm
  obtain ⟨k, hk⟩ := hpn
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso; apply hn1; rw [h0] at hk; omega
    · exact h0
  have hnk : n = 1 + p * k := by omega
  have hsq : p ^ 2 = n * m + 1 := by omega
  have hdm : p ∣ m + 1 := by
    have h1 : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
    have h2 : p ∣ p * k * m := ⟨k * m, by ring⟩
    have h3 : m + 1 + p * k * m = p ^ 2 := by rw [hsq, hnk]; ring
    have h4 : p ∣ m + 1 + p * k * m := h3 ▸ h1
    exact (Nat.dvd_add_left h2).mp h4
  obtain ⟨j, hj⟩ := hdm
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0] at hj; omega
    · exact h0
  have hmp : p - 1 ≤ m := by
    have : p ≤ p * j := Nat.le_mul_of_pos_right p hj1
    omega
  have hp1 : (p - 1) * (p + 1) = p ^ 2 - 1 := by
    have h1 : 1 ≤ p := by omega
    zify [h1, (by omega : 1 ≤ p ^ 2)]
    ring
  have hnm : n * m = (p - 1) * (p + 1) := by rw [hp1]; exact hm.symm
  have hle : n ≤ p + 1 := by
    have h5 : n * (p - 1) ≤ n * m := Nat.mul_le_mul_left n hmp
    have : n * (p - 1) ≤ (p + 1) * (p - 1) := by rw [mul_comm (p + 1), ← hnm]; exact h5
    exact Nat.le_of_mul_le_mul_right this (by omega)
  have hge : p + 1 ≤ n := by nlinarith
  omega

theorem card_statedSL_two_zmod (p : ℕ) [Fact p.Prime] :
    Nat.card (StatedSL 2 (ZMod p)) = p * (p ^ 2 - 1) := by
  have hp := (Fact.out : p.Prime)
  have hp1 : 1 ≤ p := hp.one_le
  have hp2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have hGL : Nat.card (GL (Fin 2) (ZMod p)) = p * ((p - 1) * ((p + 1) * (p - 1))) := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    rw [show p ^ 2 - 1 = (p + 1) * (p - 1) by rw [← Nat.sq_sub_sq, one_pow],
      show p ^ 2 - p = p * (p - 1) by rw [Nat.mul_sub_one, sq]]
    ring
  have hunits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hmul := Matrix.card_SL_mul_card_units (n := Fin 2) (R := ZMod p)
  rw [hGL, hunits] at hmul
  have hcard : Nat.card (SpecialLinearGroup (Fin 2) (ZMod p)) = p * ((p + 1) * (p - 1)) := by
    have hpos : 0 < p - 1 := by
      have := hp.two_le
      omega
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hmul]
    ring
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 (ZMod p)).toEquiv, hcard,
    show p ^ 2 - 1 = (p + 1) * (p - 1) by rw [← Nat.sq_sub_sq, one_pow]]

theorem index_eq_relIndex_inf_of_sup_eq_top {G : Type*} [Group G] [Finite G] {H L : Subgroup G}
    [L.Normal] (h : H ⊔ L = ⊤) : H.index = (H ⊓ L).relIndex L := by
  have h1 : (H ⊓ L).relIndex H * H.index = (H ⊓ L).index :=
    Subgroup.relIndex_mul_index inf_le_left
  have h2 : (H ⊓ L).relIndex L * L.index = (H ⊓ L).index :=
    Subgroup.relIndex_mul_index inf_le_right
  have h3 : L.index = (H ⊓ L).relIndex H := by
    rw [← Subgroup.relIndex_top_right, ← h, Subgroup.relIndex_sup_right, inf_comm,
      Subgroup.inf_relIndex_right]
  have : (H ⊓ L).IsFiniteRelIndex H := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hne : (H ⊓ L).relIndex H ≠ 0 := Subgroup.relIndex_ne_zero
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) ?_
  rw [h1, ← h2, h3, mul_comm]

theorem card_mul_relIndex_aux {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  have := Subgroup.card_mul_index (H.subgroupOf K)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at this

theorem le_comap_statedSL_of_card_eq {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] {K : Subgroup X}
    (ρ : X →* GL (Fin 2) (ZMod p)) (hcard : Nat.card (K.map ρ) = p) :
    K ≤ (StatedSL 2 (ZMod p)).comap ρ := by
  intro r hr
  have hpow : (ρ r) ^ p = 1 := by
    have := pow_card_eq_one' (G := (K.map ρ)) (x := ⟨ρ r, r, hr, rfl⟩)
    rw [hcard] at this
    exact congrArg Subtype.val this
  exact (CFSG.RankThree.SubgroupLists.mem_statedSL_iff _).mpr
    (CFSG.RankThree.SubgroupLists.det_eq_one_of_pow_eq_one _ hpow)

end CFSG.LocalAnalysis.RankThreeTheoremC

namespace CFSG.AGLEmbedding

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.PreuniquenessRankFour.Helpers CFSG.LocalAnalysis.RankThreeTheoremC

section Borel

variable {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X] {R : Sylow p X}
  {X₀ : Subgroup X}

theorem ReducedNongeneration.le_normalizer_of_ker_le (h : ReducedNongeneration p X R X₀)
    (ρ : X →* GL (Fin 2) (ZMod p)) (hker : ρ.ker ≤ (R : Subgroup X))
    (hcard : Nat.card ((R : Subgroup X).map ρ) = p) :
    X₀ ≤ Subgroup.normalizer ((R : Subgroup X) : Set X) := by
  have hp := h.prime
  have hRX₀ := h.sylow_le
  set Y : Subgroup (GL (Fin 2) (ZMod p)) := X₀.map ρ with hY
  have hRY : (R : Subgroup X).map ρ ≤ Y := Subgroup.map_mono hRX₀
  have hpY : p ∣ Nat.card Y := by
    have := Subgroup.card_dvd_of_le hRY
    rwa [hcard] at this
  rcases CFSG.RankThree.SubgroupLists.dickson_gl_two Y hpY with ⟨P, hPn, hPcard⟩ | hSL
  · have hSp : IsPGroup p (((R : Subgroup X).map ρ).subgroupOf Y) :=
      (R.isPGroup'.map ρ).comap_subtype
    obtain ⟨P', hP'⟩ := hSp.exists_le_sylow
    have := Sylow.unique_of_normal P hPn
    rw [Subsingleton.elim P' P] at hP'
    have hScard : Nat.card (((R : Subgroup X).map ρ).subgroupOf Y) = p :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRY).toEquiv).trans hcard
    have hSP : ((R : Subgroup X).map ρ).subgroupOf Y = (P : Subgroup Y) :=
      Subgroup.eq_of_le_of_card_ge hP' (by rw [hPcard, hScard])
    have hconj : ∀ x ∈ X₀, ∀ r ∈ (R : Subgroup X), x * r * x⁻¹ ∈ (R : Subgroup X) := by
      intro x hx r hr
      have hxY : ρ x ∈ Y := ⟨x, hx, rfl⟩
      have hrS : (⟨ρ r, hRY ⟨r, hr, rfl⟩⟩ : Y) ∈ ((R : Subgroup X).map ρ).subgroupOf Y :=
        Subgroup.mem_subgroupOf.mpr ⟨r, hr, rfl⟩
      have h1 := hPn.conj_mem _ (hSP ▸ hrS) ⟨ρ x, hxY⟩
      rw [← hSP, Subgroup.mem_subgroupOf] at h1
      obtain ⟨r', hr', hr'eq⟩ := h1
      have hk : r'⁻¹ * (x * r * x⁻¹) ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv]
        rw [inv_mul_eq_one]
        exact hr'eq
      have := (R : Subgroup X).mul_mem hr' (hker hk)
      rwa [mul_inv_cancel_left] at this
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hconj x hx g, fun hg => ?_⟩
    have h2 := hconj x⁻¹ (X₀.inv_mem hx) _ hg
    have e : x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g := by group
    rwa [e] at h2
  · exfalso
    set L : Subgroup X := (StatedSL 2 (ZMod p)).comap ρ with hL
    have : L.Normal := Subgroup.Normal.comap inferInstance ρ
    have hRL : (R : Subgroup X) ≤ L := le_comap_statedSL_of_card_eq ρ hcard
    have hLX₀ : L ≤ X₀ := by
      intro l hl
      obtain ⟨x₀, hx₀, hxl⟩ := hSL hl
      have hk : x₀⁻¹ * l ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxl, inv_mul_cancel]
      have := X₀.mul_mem hx₀ (hRX₀ (hker hk))
      rwa [mul_inv_cancel_left] at this
    exact not_le_of_weakCore_le h.prime R h.weakCore_le h.ne_top
      (by rw [inf_eq_left.mpr hRL]; exact h.three_le_pRank) hLX₀

theorem ReducedNongeneration.eq_normalizer_of_layer_eq_bot3 (h : ReducedNongeneration p X R X₀)
    (hlayer : CFSG.layer X = ⊥) {z : X} (hz : z ∈ Subgroup.centralizer ((R : Subgroup X) : Set X))
    (hzp : orderOf z = p) : X₀ = Subgroup.normalizer ((R : Subgroup X) : Set X) := by
  have hp := h.prime
  refine le_antisymm ?_ ((normalizer_le_weakCore_of_rank p hp _ h.three_le_pRank).trans
    h.weakCore_le)
  obtain ⟨-, E, C, hEn, hEQ, -, hEcard, hEexp, hEZ, -, -, -, -, -, -, -, -, hrel, hker, e, -⟩ :=
    h.structure_of_layer_eq_bot3 hlayer hz hzp
  have hQp : IsPGroup p (CFSG.pCore p X) := CFSG.pCore_isPGroup
  have hQn : (CFSG.pCore p X).Normal := CFSG.pCore_normal
  have hQR : CFSG.pCore p X ≤ (R : Subgroup X) := hQp.le_sylow_of_normal R
  have hkerρ : (centerQuotientActionNormal E e).ker = CFSG.pCore p X :=
    Subgroup.ext fun x => (mem_ker_centerQuotientActionNormal hEZ e).trans (hker x).symm
  refine h.le_normalizer_of_ker_le (centerQuotientActionNormal E e) (hkerρ ▸ hQR) ?_
  rw [← Subgroup.relIndex_ker, hkerρ]
  exact hrel

theorem ReducedNongeneration.index_eq_succ_of_layer_eq_bot3 (h : ReducedNongeneration p X R X₀)
    (hlayer : CFSG.layer X = ⊥) {z : X} (hz : z ∈ Subgroup.centralizer ((R : Subgroup X) : Set X))
    (hzp : orderOf z = p) : X₀.index = p + 1 := by
  have hp := h.prime
  have hX₀ := h.eq_normalizer_of_layer_eq_bot3 hlayer hz hzp
  obtain ⟨-, E, C, hEn, hEQ, -, hEcard, hEexp, hEZ, -, -, -, -, -, -, -, -, hrel, hker, e, hSL⟩ :=
    h.structure_of_layer_eq_bot3 hlayer hz hzp
  have hQp : IsPGroup p (CFSG.pCore p X) := CFSG.pCore_isPGroup
  have hQn : (CFSG.pCore p X).Normal := CFSG.pCore_normal
  have hQR : CFSG.pCore p X ≤ (R : Subgroup X) := hQp.le_sylow_of_normal R
  set ρ := centerQuotientActionNormal E e with hρ
  have hkerρ : ρ.ker = CFSG.pCore p X :=
    Subgroup.ext fun x => (mem_ker_centerQuotientActionNormal hEZ e).trans (hker x).symm
  have hcard : Nat.card ((R : Subgroup X).map ρ) = p := by
    rw [← Subgroup.relIndex_ker, hkerρ]
    exact hrel
  set S : Subgroup (GL (Fin 2) (ZMod p)) := StatedSL 2 (ZMod p) with hS
  have hSρ : S ≤ ρ.range := by
    intro a ha
    obtain ⟨g, -, rfl⟩ := hSL ha
    exact ⟨g, centerQuotientActionNormal_eq E e g⟩
  set L : Subgroup X := S.comap ρ with hL
  have : L.Normal := Subgroup.Normal.comap inferInstance ρ
  have hRL : (R : Subgroup X) ≤ L := le_comap_statedSL_of_card_eq ρ hcard
  have hLmap : L.map ρ = S := by
    rw [hL, Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hSρ
  have hF : Subgroup.normalizer ((R : Subgroup X) : Set X) ⊔ L = ⊤ :=
    Sylow.normalizer_sup_eq_top' R hRL
  have hnL := index_eq_relIndex_inf_of_sup_eq_top hF
  have hRA : (R : Subgroup X) ≤ Subgroup.normalizer ((R : Subgroup X) : Set X) ⊓ L :=
    le_inf Subgroup.le_normalizer hRL
  have hdvd1 : (Subgroup.normalizer ((R : Subgroup X) : Set X) ⊓ L).relIndex L ∣
      (R : Subgroup X).relIndex L := Subgroup.relIndex_dvd_of_le_left L hRA
  have hker_le : ρ.ker ≤ (R : Subgroup X) := hkerρ ▸ hQR
  have hRidx : (R : Subgroup X).relIndex L = ((R : Subgroup X).map ρ).relIndex S := by
    rw [← hLmap, Subgroup.relIndex_map_map, sup_eq_left.mpr hker_le,
      sup_eq_left.mpr (hker_le.trans hRL)]
  have hP₀S : (R : Subgroup X).map ρ ≤ S := by
    rw [← hLmap]
    exact Subgroup.map_mono hRL
  have hSidx : p * ((R : Subgroup X).map ρ).relIndex S = Nat.card S := by
    have := card_mul_relIndex_aux hP₀S
    rwa [hcard] at this
  have hSc : Nat.card S = p * (p ^ 2 - 1) := card_statedSL_two_zmod p
  have hrel2 : ((R : Subgroup X).map ρ).relIndex S = p ^ 2 - 1 := by
    refine Nat.eq_of_mul_eq_mul_left hp.pos ?_
    rw [hSidx, hSc]
  have hdvd : (Subgroup.normalizer ((R : Subgroup X) : Set X)).index ∣ p ^ 2 - 1 := by
    rw [hnL, ← hrel2, ← hRidx]
    exact hdvd1
  have hmod : (Subgroup.normalizer ((R : Subgroup X) : Set X)).index ≡ 1 [MOD p] := by
    have h1 := Sylow.card_eq_index_normalizer R
    have h2 := card_sylow_modEq_one p X
    rw [h1] at h2
    exact h2
  have hne : (Subgroup.normalizer ((R : Subgroup X) : Set X)).index ≠ 1 := by
    rw [Ne, Subgroup.index_eq_one, ← hX₀]
    exact h.ne_top
  rw [hX₀]
  exact eq_succ_of_dvd_sq_sub_one hp hdvd hmod hne

end Borel

end CFSG.AGLEmbedding
