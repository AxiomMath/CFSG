module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Fus
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27PAct
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Defs
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27WSpec

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
open scoped commutatorElement

structure Setup27 {G : Type} [Group G] [Finite G] (A R X O Sy Wt P : Subgroup G) (t : G) :
    Prop where
  sit : Sit27 A R X O Sy Wt t
  hnot : ¬ IsSylowOf 2 Sy (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))
  hP : PStruct27 A R P

namespace Setup27

variable {G : Type} [Group G] [Finite G] {A R X O Sy Wt P : Subgroup G} {t : G}
  (H : Setup27 A R X O Sy Wt P t)

include H

theorem P_comm_t {p : G} (hp : p ∈ P) : p * t = t * p :=
  (mem_centralizer_iff.mp H.sit.S.t_cent p (H.hP.le_A hp))

theorem le_normalizer_E : P ≤ normalizer ((R ⊔ zpowers t : Subgroup G) : Set G) := by
  intro p hp
  have hpt := H.P_comm_t hp
  have hpR : p ∈ normalizer (R : Set G) := H.hP.le_norm hp
  refine Subgroup.mem_normalizer_fintype fun e he => ?_
  have he' : e ∈ R ⊔ zpowers t := he
  rcases (H.sit.S.mem_E_iff).mp he' with heR | ⟨r, hr, rfl⟩
  · exact mem_sup_left ((mem_normalizer_iff.mp hpR e).mp heR)
  · have : p * (r * t) * p⁻¹ = (p * r * p⁻¹) * t := by
      calc p * (r * t) * p⁻¹ = p * r * p⁻¹ * (p * t * p⁻¹) := by group
        _ = (p * r * p⁻¹) * t := by rw [hpt]; group
    show p * (r * t) * p⁻¹ ∈ R ⊔ zpowers t
    rw [this]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp hpR r).mp hr)) (mem_sup_right
      (mem_zpowers t))

theorem le_normalizer_Wt : P ≤ normalizer (Wt : Set G) := by
  intro p hp
  have hpN := H.le_normalizer_E hp
  exact Subgroup.mem_normalizer_fintype fun x hx => H.sit.hWt.norm p hpN x hx

theorem le_normalizer_W : P ≤ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  refine perfect_le_normalizer_sylow (O := O) hS.O_odd hSy.isPGroup.to_inf_left
    (fun w hw o ho => hS.O_norm w (hSy.le (mem_inf.mp hw).1) o ho) H.hP.perfect ?_ ?_
  · rw [hS.sup_O_inf_Wt hSy hWt]
    exact H.le_normalizer_Wt
  · intro p hp
    rw [mem_centralizer_iff]
    intro o ho
    exact (mem_centralizer_iff.mp (hS.O_le_centralizer_A H.sit.F ho) p (H.hP.le_A hp)).symm

theorem centralizer_R_le_centralizer_W {p : G} (hp : p ∈ P) (hpR : p ∈ centralizer (R : Set G)) :
    p ∈ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  have hpA := H.hP.le_A hp
  have hRW : R ≤ Sy ⊓ Wt := hS.W_le_inf_Wt hSy hWt
  obtain ⟨r, hr, k, hk, hpe⟩ := mem_sup_centralizer hS.W_le_A
    (H.sit.F.cent p (le_normalizer hpA) (fun w hw => (mem_centralizer_iff.mp hpR w hw).symm))
  have hkp : k = r⁻¹ * p := by rw [hpe]; group
  have hkA : k ∈ A := by
    rw [hkp]
    exact A.mul_mem (A.inv_mem (hS.W_le_A hr)) hpA
  have hkO : k ∈ O := hS.inf_centralizer_A_le_O (mem_inf.mpr ⟨hkA, hk⟩)
  have hkN : k ∈ normalizer ((Sy ⊓ Wt : Subgroup G) : Set G) := by
    rw [hkp]
    exact mul_mem (inv_mem (le_normalizer (hRW hr))) (H.le_normalizer_W hp)
  have hkC := hS.centralizes_of_mem_O_normalizer hSy hkO hkN
  have hrC : r ∈ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G) :=
    mem_centralizer_iff.mpr fun x hx =>
      L34.comm_of_isElemAbelian (hS.elem_inf_Wt hSy hWt) hx (hRW hr)
  rw [hpe]
  exact mul_mem hrC hkC

omit H in
theorem card_map_mk'_eq_relIndex {M : Type*} [Group M] [Finite M] (K L : Subgroup M) [K.Normal]
    (hKL : K ≤ L) : Nat.card (L.map (QuotientGroup.mk' K)) = K.relIndex L := by
  have h := Subgroup.card_ker_mul_card_range ((QuotientGroup.mk' K).domRestrict L)
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range, QuotientGroup.ker_mk'] at h
  have hcard : Nat.card (K.subgroupOf L) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv
  have h2 := Subgroup.relIndex_mul_card K L
  rw [inf_eq_left.mpr hKL] at h2
  rw [hcard] at h
  have hpos : 0 < Nat.card K := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h, mul_comm, h2]

theorem pi_eq_one_of_mem_centralizer_W {x : G}
    (hx : x ∈ centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)) :
    pi27 (Sy ⊓ Wt) ⟨x, Subgroup.centralizer_le_normalizer _ hx⟩ = 1 := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  have hKL : (Sy ⊓ Wt).subgroupOf (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)) ≤
      (centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)).subgroupOf
        (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)) := fun y hy =>
    mem_subgroupOf.mpr (mem_centralizer_iff.mpr fun z hz =>
      L34.comm_of_isElemAbelian (hS.elem_inf_Wt hSy hWt) hz (mem_subgroupOf.mp hy))
  have hnorm : ((centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)).subgroupOf
      (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))).Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer _
  have hmapn : (((centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)).subgroupOf
      (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))).map
        (QuotientGroup.mk' ((Sy ⊓ Wt).subgroupOf
          (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))))).Normal :=
    hnorm.map _ (QuotientGroup.mk'_surjective _)
  have hodd : Odd (Nat.card (((centralizer ((Sy ⊓ Wt : Subgroup G) : Set G)).subgroupOf
      (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))).map
        (QuotientGroup.mk' ((Sy ⊓ Wt).subgroupOf
          (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)))))) := by
    rw [card_map_mk'_eq_relIndex _ _ hKL,
      Subgroup.relIndex_subgroupOf (Subgroup.centralizer_le_normalizer _)]
    exact Nat.odd_iff.mpr (by
      have := hS.not_two_dvd_relIndex_centralizer_W hSy hWt
      omega)
  have hle := le_oddCore_of_normal_odd hmapn hodd
  have hmem : (QuotientGroup.mk ⟨x, Subgroup.centralizer_le_normalizer _ hx⟩ :
      Nbar27 (Sy ⊓ Wt)) ∈ CFSG.oddCore (Nbar27 (Sy ⊓ Wt)) :=
    hle ⟨⟨x, Subgroup.centralizer_le_normalizer _ hx⟩, mem_subgroupOf.mpr hx, rfl⟩
  exact (MonoidHom.mem_ker).mp ((mem_ker_qPi _).mpr hmem)

@[expose] noncomputable def piP : ↥P →* Ntil27 (Sy ⊓ Wt) :=
  (pi27 (Sy ⊓ Wt)).comp (Subgroup.inclusion H.le_normalizer_W)

theorem piP_apply (p : ↥P) :
    piP H p = pi27 (Sy ⊓ Wt) ⟨p, H.le_normalizer_W p.2⟩ := rfl

theorem centralizes_of_pi_eq_one {p : G} (hp : p ∈ P)
    (h1 : pi27 (Sy ⊓ Wt) ⟨p, H.le_normalizer_W hp⟩ = 1) : p ∈ centralizer (R : Set G) := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  have hRW : R ≤ Sy ⊓ Wt := hS.W_le_inf_Wt hSy hWt
  have hWab := hS.elem_inf_Wt hSy hWt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥P →* MulAut ↥R, σ = conjAct27 R P H.hP.le_norm := ⟨_, rfl⟩
  have hsimple : IsSimpleGroup ↥σ.range := hσ ▸ H.hP.simple
  have hcard60 : Nat.card ↥σ.range = 60 := hσ ▸ H.hP.card
  have hσker : ∀ q : ↥P, σ q = 1 ↔ (q : G) ∈ centralizer (R : Set G) := by
    intro q
    have : σ q = R.normalizerMonoidHom ⟨q, H.hP.le_norm q.2⟩ := by rw [hσ]; rfl
    rw [this, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  have hodd : ∀ q : ↥P, piP H q = 1 → ∃ m : ℕ, Odd m ∧ (σ q) ^ m = 1 := by
    intro q hq
    obtain ⟨m, hm, hmem⟩ := exists_odd_pow_mem_of_mem_ker_qPi _
      (show (⟨q.1, H.le_normalizer_W q.2⟩ :
        ↥(normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))) ∈ (qPi ((Sy ⊓ Wt).subgroupOf
          (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)))).ker from hq)
    refine ⟨m, hm, ?_⟩
    have hqm : (q : G) ^ m ∈ Sy ⊓ Wt := mem_subgroupOf.mp hmem
    rw [← map_pow, hσker]
    exact mem_centralizer_iff.mpr fun w hw => by
      have := L34.comm_of_isElemAbelian hWab (hRW hw) hqm
      simpa using this
  have hTn : ((piP H).ker.map σ.rangeRestrict).Normal :=
    Subgroup.Normal.map inferInstance _ (MonoidHom.rangeRestrict_surjective σ)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((piP H).ker.map σ.rangeRestrict) with hT | hT
  · have hmem : (⟨p, hp⟩ : ↥P) ∈ (piP H).ker := h1
    have h2 : σ.rangeRestrict ⟨p, hp⟩ ∈ (piP H).ker.map σ.rangeRestrict :=
      Subgroup.mem_map_of_mem _ hmem
    rw [hT, Subgroup.mem_bot] at h2
    exact (hσker ⟨p, hp⟩).mp (congrArg Subtype.val h2)
  · exfalso
    have h60 : 2 ∣ Nat.card ↥σ.range := by
      rw [hcard60]
      norm_num
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥σ.range) 2 h60
    have hgT : g ∈ (piP H).ker.map σ.rangeRestrict := hT ▸ Subgroup.mem_top g
    obtain ⟨q, hq, hqg⟩ := hgT
    obtain ⟨m, hm, hqm⟩ := hodd q hq
    have hgm : g ^ m = 1 := by
      rw [← hqg, ← map_pow]
      apply Subtype.ext
      show σ (q ^ m) = 1
      rw [map_pow]
      exact hqm
    have hdvd : 2 ∣ m := hg ▸ orderOf_dvd_of_pow_eq_one hgm
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hdvd)

@[expose] noncomputable def X27 : Subgroup (Ntil27 (Sy ⊓ Wt)) := (piP H).range

@[expose] noncomputable def ttilde27 : Ntil27 (Sy ⊓ Wt) :=
  tilde27 (Sy ⊓ Wt) (H.sit.S.t_mem_normalizer_inf_Wt H.sit.hSy H.sit.hWt)

theorem ttilde27_eq : H.ttilde27 =
    pi27 (Sy ⊓ Wt) ⟨t, H.sit.S.t_mem_normalizer_inf_Wt H.sit.hSy H.sit.hWt⟩ := rfl

theorem ker_piP_eq : (piP H).ker = (conjAct27 R P H.hP.le_norm).ker := by
  have hker : ∀ q : ↥P, conjAct27 R P H.hP.le_norm q = 1 ↔ (q : G) ∈ centralizer (R : Set G) := by
    intro q
    have : conjAct27 R P H.hP.le_norm q = R.normalizerMonoidHom ⟨q, H.hP.le_norm q.2⟩ := rfl
    rw [this, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  ext q
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker]
  constructor
  · intro h
    exact H.centralizes_of_pi_eq_one q.2 h
  · intro h
    exact H.pi_eq_one_of_mem_centralizer_W (H.centralizer_R_le_centralizer_W q.2 h)

theorem X27_equiv : Nonempty (↥H.X27 ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e₁⟩ := rangeEquiv_of_ker_eq (piP H) (conjAct27 R P H.hP.le_norm) H.ker_piP_eq
  have := H.hP.simple
  obtain ⟨e₂⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five H.hP.card
  exact ⟨e₁.trans e₂⟩

theorem ttilde27_order : orderOf H.ttilde27 = 2 := by
  have hS := H.sit.S
  have htN := hS.t_mem_normalizer_inf_Wt H.sit.hSy H.sit.hWt
  have hsq : H.ttilde27 * H.ttilde27 = 1 := by
    rw [H.ttilde27_eq, ← map_mul]
    have : (⟨t, htN⟩ : ↥(normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))) * ⟨t, htN⟩ = 1 :=
      Subtype.ext hS.t_sq
    rw [this, map_one]
  have hne : H.ttilde27 ≠ 1 :=
    pi27_ne_one_of_not_mem htN hS.t_sq (IsSetting25.t_not_mem_inf_Wt H.sit.hWt)
  exact orderOf_eq_prime (by rw [sq]; exact hsq) hne

theorem ttilde27_comm_X {x : Ntil27 (Sy ⊓ Wt)} (hx : x ∈ H.X27) :
    x * H.ttilde27 = H.ttilde27 * x := by
  obtain ⟨p, rfl⟩ := hx
  rw [H.ttilde27_eq, piP_apply, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (H.P_comm_t p.2)

theorem X27_normal {g : Ntil27 (Sy ⊓ Wt)} (hg : g ∈ centralizer ({H.ttilde27} :
    Set (Ntil27 (Sy ⊓ Wt)))) {x : Ntil27 (Sy ⊓ Wt)} (hx : x ∈ H.X27) : g * x * g⁻¹ ∈ H.X27 := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  obtain ⟨c, hct, rfl⟩ := hS.exists_mem_C₂_of_mem_centralizer_pi hSy hWt hg
  obtain ⟨p, rfl⟩ := hx
  have hcA : (c : G) ∈ normalizer (A : Set G) := hS.cent_t hct
  have hcR := (hS.mem_normalizer_of_mem_normalizer_W_cent hSy hWt c.2 hct).1
  have hmem : (c : G) * (p : G) * (c : G)⁻¹ ∈ P := H.hP.char _ ⟨hcA, hcR⟩ p p.2
  refine ⟨⟨(c : G) * (p : G) * (c : G)⁻¹, hmem⟩, ?_⟩
  have h : pi27 (Sy ⊓ Wt) ⟨(c : G) * (p : G) * (c : G)⁻¹, H.le_normalizer_W hmem⟩ =
      pi27 (Sy ⊓ Wt) c * pi27 (Sy ⊓ Wt) ⟨p, H.le_normalizer_W p.2⟩ * (pi27 (Sy ⊓ Wt) c)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  exact h

theorem two_elt_mem_zpowers_ttilde {z : Ntil27 (Sy ⊓ Wt)}
    (hzt : z ∈ centralizer ({H.ttilde27} : Set (Ntil27 (Sy ⊓ Wt))))
    (hzX : z ∈ centralizer ((H.X27 : Subgroup (Ntil27 (Sy ⊓ Wt))) : Set (Ntil27 (Sy ⊓ Wt))))
    (h2 : ∃ n : ℕ, orderOf z = 2 ^ n) : z ∈ zpowers H.ttilde27 := by
  have hS := H.sit.S
  have hSy := H.sit.hSy
  have hWt := H.sit.hWt
  have htN := hS.t_mem_normalizer_inf_Wt hSy hWt
  have hRW : R ≤ Sy ⊓ Wt := hS.W_le_inf_Wt hSy hWt
  obtain ⟨c₀, hc₀t, hc₀z⟩ := hS.exists_mem_C₂_of_mem_centralizer_pi hSy hWt hzt
  obtain ⟨n, hn⟩ := h2
  obtain ⟨c, hc, hpic, m, hcm⟩ := exists_two_part_lift (pi27 (Sy ⊓ Wt)) c₀
    ⟨n, by rw [hc₀z]; exact hn⟩
  have hpicz : pi27 (Sy ⊓ Wt) c = z := hpic.trans hc₀z
  have hct : (c : G) ∈ centralizer ({t} : Set G) := by
    have : zpowers c₀ ≤ (centralizer ({t} : Set G)).subgroupOf
        (normalizer ((Sy ⊓ Wt : Subgroup G) : Set G)) :=
      Subgroup.zpowers_le.mpr (mem_subgroupOf.mpr hc₀t)
    exact mem_subgroupOf.mp (this hc)
  have hcA : (c : G) ∈ normalizer (A : Set G) := hS.cent_t hct
  have hcR := (hS.mem_normalizer_of_mem_normalizer_W_cent hSy hWt c.2 hct).1
  have hc2 : ∃ k : ℕ, orderOf (c : G) = 2 ^ k := ⟨m, by rw [Subgroup.orderOf_coe]; exact hcm⟩
  have hcpow : (c : G) ^ (2 ^ m) = 1 := by
    have h := pow_orderOf_eq_one (c : G)
    rwa [Subgroup.orderOf_coe, hcm] at h
  have hker : ∀ y : ↥(normalizer (R : Set G)),
      R.normalizerMonoidHom y = 1 ↔ (y : G) ∈ centralizer (R : Set G) := by
    intro y
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  have hcomm : ∀ p : ↥P, R.normalizerMonoidHom ⟨(c : G), hcR⟩ *
      conjAct27 R P H.hP.le_norm p =
      conjAct27 R P H.hP.le_norm p * R.normalizerMonoidHom ⟨(c : G), hcR⟩ := by
    intro p
    have hmem : (c : G) * (p : G) * (c : G)⁻¹ * (p : G)⁻¹ ∈ P :=
      P.mul_mem (H.hP.char _ ⟨hcA, hcR⟩ p p.2) (P.inv_mem p.2)
    have hxz : piP H p * z = z * piP H p := mem_centralizer_iff.mp hzX (piP H p) ⟨p, rfl⟩
    have hel : (⟨(c : G) * (p : G) * (c : G)⁻¹ * (p : G)⁻¹, H.le_normalizer_W hmem⟩ :
        ↥(normalizer ((Sy ⊓ Wt : Subgroup G) : Set G))) =
        c * ⟨(p : G), H.le_normalizer_W p.2⟩ * c⁻¹ * ⟨(p : G), H.le_normalizer_W p.2⟩⁻¹ :=
      Subtype.ext rfl
    have h1 : pi27 (Sy ⊓ Wt) ⟨(c : G) * (p : G) * (c : G)⁻¹ * (p : G)⁻¹,
        H.le_normalizer_W hmem⟩ = 1 := by
      rw [hel, map_mul, map_mul, map_mul, map_inv, map_inv, hpicz, ← piP_apply H p]
      calc z * piP H p * z⁻¹ * (piP H p)⁻¹ = (piP H p * z) * z⁻¹ * (piP H p)⁻¹ := by
            rw [hxz]
        _ = 1 := by group
    have hcom := H.centralizes_of_pi_eq_one hmem h1
    have h2 : R.normalizerMonoidHom ⟨(c : G), hcR⟩ * R.normalizerMonoidHom
        ⟨(p : G), H.hP.le_norm p.2⟩ * (R.normalizerMonoidHom ⟨(c : G), hcR⟩)⁻¹ *
        (R.normalizerMonoidHom ⟨(p : G), H.hP.le_norm p.2⟩)⁻¹ = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact (hker _).mpr hcom
    show R.normalizerMonoidHom ⟨(c : G), hcR⟩ * R.normalizerMonoidHom
        ⟨(p : G), H.hP.le_norm p.2⟩ = R.normalizerMonoidHom ⟨(p : G), H.hP.le_norm p.2⟩ *
        R.normalizerMonoidHom ⟨(c : G), hcR⟩
    calc R.normalizerMonoidHom ⟨(c : G), hcR⟩ * R.normalizerMonoidHom
          ⟨(p : G), H.hP.le_norm p.2⟩ = (R.normalizerMonoidHom ⟨(c : G), hcR⟩ *
          R.normalizerMonoidHom ⟨(p : G), H.hP.le_norm p.2⟩ *
          (R.normalizerMonoidHom ⟨(c : G), hcR⟩)⁻¹ *
          (R.normalizerMonoidHom ⟨(p : G), H.hP.le_norm p.2⟩)⁻¹) *
          (R.normalizerMonoidHom ⟨(p : G), H.hP.le_norm p.2⟩ *
          R.normalizerMonoidHom ⟨(c : G), hcR⟩) := by group
      _ = _ := by rw [h2, one_mul]
  have hg3 := H.hP.cent _ hcomm
  have hg2 : (R.normalizerMonoidHom ⟨(c : G), hcR⟩) ^ (2 ^ m) = 1 := by
    rw [← map_pow]
    have : (⟨(c : G), hcR⟩ : ↥(normalizer (R : Set G))) ^ (2 ^ m) = 1 := Subtype.ext hcpow
    rw [this, map_one]
  have hg1 : R.normalizerMonoidHom ⟨(c : G), hcR⟩ = 1 := by
    have hcop : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left m (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hg2)
      (orderOf_dvd_of_pow_eq_one hg3))
  have hcRc : (c : G) ∈ centralizer (R : Set G) := (hker _).mp hg1
  have hle : (R ⊔ zpowers t : Subgroup G) ≤ centralizer ({(c : G)} : Set G) := by
    refine sup_le (fun r hr => ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp hcRc r hr
    · rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_singleton_iff.mp hct).symm
  have hcE : (c : G) ∈ centralizer ((R ⊔ zpowers t : Subgroup G) : Set G) :=
    mem_centralizer_iff.mpr fun e he => mem_centralizer_singleton_iff.mp (hle he)
  have hcEmem := hS.two_elt_mem_E hcE hc2
  rw [← hpicz]
  rcases hS.mem_E_iff.mp hcEmem with hcRmem | ⟨r, hr, hcr⟩
  · have h1 : pi27 (Sy ⊓ Wt) c = 1 := pi27_eq_one_of_mem (hRW hcRmem)
    rw [h1]
    exact one_mem _
  · have : c = ⟨r, le_normalizer (hRW hr)⟩ * ⟨t, htN⟩ := Subtype.ext hcr
    rw [this, map_mul, pi27_eq_one_of_mem (hRW hr), one_mul]
    exact mem_zpowers _

theorem cent_two27 : padicValNat 2 (Nat.card ↥(centralizer ({H.ttilde27} :
    Set (Ntil27 (Sy ⊓ Wt))) ⊓ centralizer ((H.X27 : Subgroup (Ntil27 (Sy ⊓ Wt))) :
      Set (Ntil27 (Sy ⊓ Wt))))) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup (Ntil27 (Sy ⊓ Wt)), Z = centralizer ({H.ttilde27} :
      Set (Ntil27 (Sy ⊓ Wt))) ⊓ centralizer ((H.X27 : Subgroup (Ntil27 (Sy ⊓ Wt))) :
        Set (Ntil27 (Sy ⊓ Wt))) := ⟨_, rfl⟩
  rw [← hZ]
  have hmemiff : ∀ x : Ntil27 (Sy ⊓ Wt), x ∈ Z ↔ (x ∈ centralizer ({H.ttilde27} :
      Set (Ntil27 (Sy ⊓ Wt))) ∧ x ∈ centralizer ((H.X27 : Subgroup (Ntil27 (Sy ⊓ Wt))) :
        Set (Ntil27 (Sy ⊓ Wt)))) := fun x => by
    rw [hZ]
    exact mem_inf
  have hmem : H.ttilde27 ∈ Z := (hmemiff _).mpr ⟨mem_centralizer_singleton_iff.mpr rfl,
    mem_centralizer_iff.mpr fun x hx => H.ttilde27_comm_X hx⟩
  have hdvd : 2 ∣ Nat.card Z := by
    have := Subgroup.orderOf_dvd_natCard Z hmem
    rwa [H.ttilde27_order] at this
  obtain ⟨T⟩ : Nonempty (Sylow 2 Z) := inferInstance
  have hT : (T : Subgroup Z).map Z.subtype ≤ zpowers H.ttilde27 := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp T.isPGroup' ⟨y, hy⟩
    have hk' : orderOf (y : Ntil27 (Sy ⊓ Wt)) = 2 ^ k := by
      rw [Subgroup.orderOf_coe, ← Subgroup.orderOf_mk y hy]
      exact hk
    have hyZ := (hmemiff (y : Ntil27 (Sy ⊓ Wt))).mp y.2
    exact H.two_elt_mem_zpowers_ttilde hyZ.1 hyZ.2 ⟨k, hk'⟩
  have hcard : Nat.card T ≤ 2 := by
    have h1 := Subgroup.card_le_of_le hT
    rw [Subgroup.card_map_of_injective Z.subtype_injective, Nat.card_zpowers,
      H.ttilde27_order] at h1
    exact h1
  rw [Sylow.card_eq_multiplicity] at hcard
  have hv1 : 1 ≤ (Nat.card Z).factorization 2 :=
    (Nat.Prime.factorization_pos_of_dvd Nat.prime_two (Nat.card_pos.ne') hdvd)
  have hv2 : (Nat.card Z).factorization 2 ≤ 1 := by
    by_contra hlt
    have hlt' : 2 ≤ (Nat.card Z).factorization 2 := by omega
    have : 2 ^ 2 ≤ 2 ^ (Nat.card Z).factorization 2 := Nat.pow_le_pow_right (by norm_num) hlt'
    omega
  rw [← Nat.factorization_def (Nat.card Z) Nat.prime_two]
  omega

theorem not_sylow27 : padicValNat 2 (Nat.card ↥(centralizer ({H.ttilde27} :
    Set (Ntil27 (Sy ⊓ Wt))))) < padicValNat 2 (Nat.card (Ntil27 (Sy ⊓ Wt))) :=
  H.sit.S.padicValNat_centralizer_pi_lt H.sit.hSy H.sit.hWt H.hnot

omit H in
theorem lieModel_of_mulEquiv_alt5 {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : LieModel X .PSL 2 2 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl (by rw [hK]; norm_num))
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, hK, ⟨e.trans e5.symm⟩⟩

theorem local27 :
    Local27 (Ntil27 (Sy ⊓ Wt)) H.X27 H.ttilde27 where
  oddCore_bot := oddCore_qPi_bot _
  model := by
    obtain ⟨e⟩ := H.X27_equiv
    exact lieModel_of_mulEquiv_alt5 e
  t_order := H.ttilde27_order
  t_cent := fun x hx => H.ttilde27_comm_X hx
  X_normal := fun g hg x hx => H.X27_normal hg hx
  cent_two := H.cent_two27
  not_sylow := H.not_sylow27

end Setup27

end CFSG.OddStandard.Seitz77
