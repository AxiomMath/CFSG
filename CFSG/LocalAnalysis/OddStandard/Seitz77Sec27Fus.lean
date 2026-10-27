module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Syl
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Quot
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Act

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

namespace IsSetting25

variable {G : Type} [Group G] [Finite G] {A R X O : Subgroup G} {t : G}
  (S : IsSetting25 A R t X O)

section Fus

variable {Sy Wt : Subgroup G}
  (hSy : IsSylowOf 2 Sy (normalizer ((R ⊔ zpowers t : Subgroup G) : Set G)))
  (hWt : WtSpec R t X O Wt)

include S hSy hWt

omit S in
theorem Sy_le_normalizer_inf_Wt : Sy ≤ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
  intro s hs
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  have h := (normal_inf_Wt hSy hWt).conj_mem ⟨w, (mem_inf.mp hw).1⟩ (mem_subgroupOf.mpr hw)
    ⟨s, hs⟩
  exact mem_subgroupOf.mp h

theorem t_mem_normalizer_inf_Wt : t ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
  Sy_le_normalizer_inf_Wt hSy hWt (S.E_le_sylow hSy (mem_sup_right (mem_zpowers t)))

theorem mem_R_of_mul_t_sq {c : G} (hc : c ∈ Sy ⊓ Wt) (h : (c * t) * (c * t) = 1) : c ∈ R := by
  have hWab := S.elem_inf_Wt hSy hWt
  have hsq : c * c = 1 := by
    have := hWab.2 c hc
    rwa [sq] at this
  have h2 : c * (t * c * t⁻¹) = 1 := by
    have : (c * t) * (c * t) = c * (t * c * t⁻¹) * (t * t) := by group
    rw [this, S.t_sq, mul_one] at h
    exact h
  have h3 : t * c * t⁻¹ = c := by
    rw [eq_inv_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right hsq]
  rw [← S.inf_Wt_inf_centralizer_t hSy hWt]
  refine mem_inf.mpr ⟨hc, mem_centralizer_singleton_iff.mpr ?_⟩
  calc c * t = (t * c * t⁻¹) * t := by rw [h3]
    _ = t * c := by group

theorem exists_w_cent_of_comm_mem_W {n : G} (hc : n * t * n⁻¹ * t⁻¹ ∈ Sy ⊓ Wt) :
    ∃ w ∈ Sy ⊓ Wt, w⁻¹ * n ∈ centralizer ({t} : Set G) := by
  have hsq : (n * t * n⁻¹ * t⁻¹ * t) * (n * t * n⁻¹ * t⁻¹ * t) = 1 := by
    calc (n * t * n⁻¹ * t⁻¹ * t) * (n * t * n⁻¹ * t⁻¹ * t) = n * (t * t) * n⁻¹ := by group
      _ = 1 := by rw [S.t_sq]; group
  have hcR : n * t * n⁻¹ * t⁻¹ ∈ R := S.mem_R_of_mul_t_sq hSy hWt hc hsq
  obtain ⟨w, hw, hwt⟩ := S.exists_conj_eq hSy hWt hcR
  refine ⟨w, hw, mem_centralizer_singleton_iff.mpr ?_⟩
  have h1 : n * t * n⁻¹ = t * (n * t * n⁻¹ * t⁻¹) := by
    have : t * (n * t * n⁻¹ * t⁻¹) = (n * t * n⁻¹ * t⁻¹) * t := S.t_comm_W hcR
    rw [this]
    group
  calc w⁻¹ * n * t = w⁻¹ * (n * t * n⁻¹) * n := by group
    _ = w⁻¹ * (w * t * w⁻¹) * n := by rw [h1, hwt]
    _ = t * (w⁻¹ * n) := by group

theorem exists_w_cent_of_mem_normalizer {n : G}
    (hn : n ∈ normalizer ((R ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ w ∈ Sy ⊓ Wt, w⁻¹ * n ∈ centralizer ({t} : Set G) := by
  apply S.exists_w_cent_of_comm_mem_W hSy hWt
  obtain ⟨v, hv, hnt⟩ := S.conj_t n hn
  have : n * t * n⁻¹ * t⁻¹ = v := by
    rw [hnt]
    have : t * v = v * t := S.t_comm_W hv
    rw [this]
    group
  rw [this]
  exact S.W_le_inf_Wt hSy hWt hv

theorem mem_normalizer_of_mem_normalizer_W_cent {c : G}
    (hcW : c ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))
    (hct : c ∈ centralizer ({t} : Set G)) :
    c ∈ normalizer (R : Set G) ∧ c ∈ normalizer ((R ⊔ zpowers t : Subgroup G) : Set G) := by
  have hct' : c * t = t * c := mem_centralizer_singleton_iff.mp hct
  have hcR : ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
    intro r hr
    have hW : c * r * c⁻¹ ∈ Sy ⊓ Wt :=
      (mem_normalizer_iff.mp hcW r).mp (S.W_le_inf_Wt hSy hWt hr)
    have hrt : r * t = t * r := (S.t_comm_W hr).symm
    rw [← S.inf_Wt_inf_centralizer_t hSy hWt]
    refine mem_inf.mpr ⟨hW, mem_centralizer_singleton_iff.mpr ?_⟩
    calc c * r * c⁻¹ * t = c * r * (c⁻¹ * t) := by rw [mul_assoc (c * r)]
      _ = c * r * (t * c⁻¹) := by
        have : c⁻¹ * t = t * c⁻¹ := (show Commute c t from hct').inv_left.eq
        rw [this]
      _ = c * (r * t) * c⁻¹ := by group
      _ = c * (t * r) * c⁻¹ := by rw [hrt]
      _ = t * (c * r * c⁻¹) := by
        calc c * (t * r) * c⁻¹ = (c * t) * r * c⁻¹ := by group
          _ = (t * c) * r * c⁻¹ := by rw [hct']
          _ = t * (c * r * c⁻¹) := by group
  have hN : c ∈ normalizer (R : Set G) :=
    Subgroup.mem_normalizer_fintype fun r hr => hcR r hr
  refine ⟨hN, Subgroup.mem_normalizer_fintype fun e he => ?_⟩
  have he' : e ∈ R ⊔ zpowers t := he
  rcases (S.mem_E_iff).mp he' with heR | ⟨r, hr, rfl⟩
  · exact mem_sup_left (hcR e heR)
  · have : c * (r * t) * c⁻¹ = (c * r * c⁻¹) * t := by
      calc c * (r * t) * c⁻¹ = c * r * (c⁻¹ * c) * t * c⁻¹ := by group
        _ = c * r * c⁻¹ * (c * t * c⁻¹) := by group
        _ = (c * r * c⁻¹) * t := by
          rw [hct']
          group
    show c * (r * t) * c⁻¹ ∈ R ⊔ zpowers t
    rw [this]
    exact mul_mem (mem_sup_left (hcR r hr)) (mem_sup_right (mem_zpowers t))

end Fus

end IsSetting25

theorem padicValNat_card_qPi_add {M : Type*} [Group M] [Finite M] (K : Subgroup M) [K.Normal] :
    padicValNat 2 (Nat.card ((M ⧸ K) ⧸ CFSG.oddCore (M ⧸ K))) + padicValNat 2 (Nat.card K) =
      padicValNat 2 (Nat.card M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card (qPi K).ker * Nat.card ((M ⧸ K) ⧸ CFSG.oddCore (M ⧸ K)) = Nat.card M :=
    Subgroup.card_ker_mul_card_of_surjective (qPi_surjective K)
  rw [card_ker_qPi K] at h1
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hO0 : Nat.card (CFSG.oddCore (M ⧸ K)) ≠ 0 := Nat.card_pos.ne'
  have hQ0 : Nat.card ((M ⧸ K) ⧸ CFSG.oddCore (M ⧸ K)) ≠ 0 := Nat.card_pos.ne'
  have hodd : padicValNat 2 (Nat.card (CFSG.oddCore (M ⧸ K))) = 0 :=
    padicValNat.eq_zero_of_not_dvd (Odd.not_two_dvd_nat odd_card_oddCore_s27)
  rw [← h1, padicValNat.mul (mul_ne_zero hK0 hO0) hQ0, padicValNat.mul hK0 hO0, hodd]
  omega

theorem card_map_qPi_mul_card {M : Type*} [Group M] [Finite M] (K : Subgroup M) [K.Normal]
    {T : Subgroup M} (hT : IsPGroup 2 T) (hKT : K ≤ T) :
    Nat.card (T.map (qPi K)) * Nat.card K = Nat.card T := by
  have h := Subgroup.card_ker_mul_card_range ((qPi K).domRestrict T)
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range] at h
  have hsub : (qPi K).ker.subgroupOf T = K.subgroupOf T := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact ⟨fun hx => inf_ker_qPi_le K hT ⟨x.2, hx⟩, fun hx => le_ker_qPi K hx⟩
  have hcard : Nat.card (K.subgroupOf T) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKT).toEquiv
  rw [hsub, hcard] at h
  rw [mul_comm]
  exact h

theorem padicValNat_image_lt {M : Type*} [Group M] [Finite M] (K : Subgroup M) [K.Normal]
    (hK : IsPGroup 2 K) {Y T : Subgroup M} (hT : IsSylowOf 2 T Y) (hKT : K ≤ T)
    (hnot : ¬ IsSylowOf 2 T ⊤) :
    padicValNat 2 (Nat.card (Y.map (qPi K))) <
      padicValNat 2 (Nat.card ((M ⧸ K) ⧸ CFSG.oddCore (M ⧸ K))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTP : IsPGroup 2 T := hT.isPGroup
  have h1 := padicValNat_card_qPi_add K
  have hS := L34.isSylowOf_map hT (qPi K)
  have h2 : Nat.card (T.map (qPi K)) = 2 ^ padicValNat 2 (Nat.card (Y.map (qPi K))) := by
    rw [hS.card_eq, Nat.factorization_def _ Nat.prime_two]
  have h3 := card_map_qPi_mul_card K hTP hKT
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hTP
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hK
  have hvK : padicValNat 2 (Nat.card K) = b := by rw [hb, padicValNat.prime_pow]
  have hMne : Nat.card M ≠ 0 := Nat.card_pos.ne'
  have hdvd : 2 ^ a ∣ Nat.card M := ha ▸ Subgroup.card_subgroup_dvd_card T
  have hale : a ≤ padicValNat 2 (Nat.card M) := (padicValNat_dvd_iff_le hMne).mp hdvd
  have hane : a ≠ padicValNat 2 (Nat.card M) := by
    intro hEq
    apply hnot
    apply isSylowOf_of_card le_top
    rw [Subgroup.card_top, Nat.factorization_def _ Nat.prime_two, ha, ← hEq]
  rw [h2, hb, ha, ← pow_add] at h3
  have h4 := Nat.pow_right_injective (le_refl 2) h3
  omega


section Pi

variable {G : Type} [Group G] [Finite G]

abbrev Nbar27 (W : Subgroup G) : Type :=
  ↥(normalizer (W : Set G)) ⧸ W.subgroupOf (normalizer (W : Set G))

abbrev Ntil27 (W : Subgroup G) : Type := Nbar27 W ⧸ CFSG.oddCore (Nbar27 W)

@[expose] def pi27 (W : Subgroup G) : ↥(normalizer (W : Set G)) →* Ntil27 W :=
  qPi (W.subgroupOf (normalizer (W : Set G)))

@[expose] def tilde27 (W : Subgroup G) {t : G} (ht : t ∈ normalizer (W : Set G)) : Ntil27 W :=
  pi27 W ⟨t, ht⟩

omit [Finite G] in
theorem pi27_surjective (W : Subgroup G) : Function.Surjective (pi27 W) :=
  qPi_surjective _

omit [Finite G] in
theorem pi27_eq_one_of_mem {W : Subgroup G} {w : G} (hw : w ∈ W) :
    pi27 W ⟨w, le_normalizer hw⟩ = 1 :=
  (MonoidHom.mem_ker).mp
    (le_ker_qPi (W.subgroupOf (normalizer (W : Set G))) (mem_subgroupOf.mpr hw))

theorem pi27_ne_one_of_not_mem {W : Subgroup G} {t : G} (ht : t ∈ normalizer (W : Set G))
    (ht2 : t * t = 1) (htW : t ∉ W) : pi27 W ⟨t, ht⟩ ≠ 1 := by
  intro h
  have hker : (⟨t, ht⟩ : ↥(normalizer (W : Set G))) ∈
      (qPi (W.subgroupOf (normalizer (W : Set G)))).ker := h
  obtain ⟨m, hm, hmem⟩ := exists_odd_pow_mem_of_mem_ker_qPi _ hker
  obtain ⟨a, rfl⟩ := hm
  have hpow : (⟨t, ht⟩ : ↥(normalizer (W : Set G))) ^ (2 * a + 1) = ⟨t, ht⟩ := by
    have h2 : (⟨t, ht⟩ : ↥(normalizer (W : Set G))) * ⟨t, ht⟩ = 1 := Subtype.ext ht2
    rw [pow_succ, pow_mul, sq, h2, one_pow, one_mul]
  rw [hpow] at hmem
  exact htW (mem_subgroupOf.mp hmem)

namespace IsSetting25

variable {A R X O : Subgroup G} {t : G} (S : IsSetting25 A R t X O) {Sy Wt : Subgroup G}
  (hSy : IsSylowOf 2 Sy (normalizer ((R ⊔ zpowers t : Subgroup G) : Set G)))
  (hWt : WtSpec R t X O Wt)

include S hSy hWt

theorem exists_mem_C₂_of_mem_centralizer_pi
    {y : Ntil27 (Sy ⊓ Wt)}
    (hy : y ∈ centralizer ({pi27 (Sy ⊓ Wt) ⟨t, S.t_mem_normalizer_inf_Wt hSy hWt⟩} :
      Set (Ntil27 (Sy ⊓ Wt)))) :
    ∃ c : ↥(normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)),
      (c : G) ∈ centralizer ({t} : Set G) ∧ pi27 (Sy ⊓ Wt) c = y := by
  have htN := S.t_mem_normalizer_inf_Wt hSy hWt
  have hty : (⟨t, htN⟩ : ↥(normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))) *
      ⟨t, htN⟩ ∈ (Sy ⊓ Wt).subgroupOf (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)) := by
    have : (⟨t, htN⟩ : ↥(normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))) * ⟨t, htN⟩ = 1 :=
      Subtype.ext S.t_sq
    rw [this]
    exact one_mem _
  obtain ⟨x, hxy, hx⟩ := exists_pre_centralizer_qPi
    ((Sy ⊓ Wt).subgroupOf (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))) hty
    (pi27_ne_one_of_not_mem htN S.t_sq (t_not_mem_inf_Wt hWt)) hy
  have hx' : (x : G) * t * (x : G)⁻¹ * t⁻¹ ∈ Sy ⊓ Wt := mem_subgroupOf.mp hx
  obtain ⟨w, hw, hwx⟩ := S.exists_w_cent_of_comm_mem_W hSy hWt hx'
  refine ⟨⟨w⁻¹, le_normalizer ((Sy ⊓ Wt).inv_mem hw)⟩ * x, hwx, ?_⟩
  rw [map_mul, pi27_eq_one_of_mem ((Sy ⊓ Wt).inv_mem hw), one_mul]
  exact hxy

theorem centralizer_pi_eq_map :
    centralizer ({pi27 (Sy ⊓ Wt) ⟨t, S.t_mem_normalizer_inf_Wt hSy hWt⟩} :
        Set (Ntil27 (Sy ⊓ Wt))) =
      ((normalizer ((R ⊔ zpowers t : Subgroup G) : Set G)).subgroupOf
        (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))).map (pi27 (Sy ⊓ Wt)) := by
  have htN := S.t_mem_normalizer_inf_Wt hSy hWt
  ext y
  constructor
  · intro hy
    obtain ⟨c, hct, rfl⟩ := S.exists_mem_C₂_of_mem_centralizer_pi hSy hWt hy
    refine ⟨c, ?_, rfl⟩
    exact (S.mem_normalizer_of_mem_normalizer_W_cent hSy hWt c.2 hct).2
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨w, hw, hwn⟩ := S.exists_w_cent_of_mem_normalizer hSy hWt (mem_subgroupOf.mp hn)
    obtain ⟨c, hc⟩ : ∃ c : ↥(normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)),
        c = ⟨w⁻¹ * n, mul_mem (inv_mem (le_normalizer hw)) n.2⟩ := ⟨_, rfl⟩
    have hnc : (⟨w, le_normalizer hw⟩ :
        ↥(normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))) * c = n := by
      apply Subtype.ext
      rw [hc]
      simp
    have hpn : pi27 (Sy ⊓ Wt) n = pi27 (Sy ⊓ Wt) c := by
      rw [← hnc, map_mul, pi27_eq_one_of_mem hw, one_mul]
    have hcomm : c * ⟨t, htN⟩ = ⟨t, htN⟩ * c := by
      apply Subtype.ext
      rw [hc]
      exact mem_centralizer_singleton_iff.mp hwn
    rw [mem_centralizer_singleton_iff, hpn, ← map_mul, ← map_mul, hcomm]

theorem padicValNat_centralizer_pi_lt
    (hnot : ¬ IsSylowOf 2 Sy (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))) :
    padicValNat 2 (Nat.card ↥(centralizer ({tilde27 (Sy ⊓ Wt) (S.t_mem_normalizer_inf_Wt hSy hWt)} :
        Set (Ntil27 (Sy ⊓ Wt))))) < padicValNat 2 (Nat.card (Ntil27 (Sy ⊓ Wt))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyN₁ : Sy ≤ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
    Sy_le_normalizer_inf_Wt hSy hWt
  rw [show tilde27 (Sy ⊓ Wt) (S.t_mem_normalizer_inf_Wt hSy hWt) =
    pi27 (Sy ⊓ Wt) ⟨t, S.t_mem_normalizer_inf_Wt hSy hWt⟩ from rfl, S.centralizer_pi_eq_map hSy hWt]
  have hK2 : IsPGroup 2 ↥((Sy ⊓ Wt).subgroupOf (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))) :=
    (hSy.isPGroup.to_inf_left : IsPGroup 2 ↥(Sy ⊓ Wt)).comap_subtype
  have hT : IsSylowOf 2 (Sy.subgroupOf (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)))
      ((normalizer ((R ⊔ zpowers t : Subgroup G) : Set G)).subgroupOf
        (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))) := by
    rw [← isSylowOf_map_subtype_iff (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))]
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hSyN₁]
    exact hSy.of_le (le_inf hSy.le hSyN₁) inf_le_left
  have hKT : (Sy ⊓ Wt).subgroupOf (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)) ≤
      Sy.subgroupOf (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)) := fun x hx =>
    mem_subgroupOf.mpr (mem_inf.mp (mem_subgroupOf.mp hx)).1
  have hnot' : ¬ IsSylowOf 2 (Sy.subgroupOf (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))) ⊤ := by
    intro h
    apply hnot
    have h' := (isSylowOf_map_subtype_iff (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))).mpr h
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSyN₁, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h'
    exact h'
  exact padicValNat_image_lt _ hK2 hT hKT hnot'

end IsSetting25

end Pi

end CFSG.OddStandard.Seitz77
