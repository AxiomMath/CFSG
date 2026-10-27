module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFySignA

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

variable {G : Type} [Group G] [Finite G] {t r : G} {Θ : HModel →* G}

@[expose] noncomputable def FyConf.tauX (h : FyConf t r Θ) : RedX r :=
  h.Phi (DihedralGroup.r 2, 1, 1)

theorem FyConf.tauX_sq (h : FyConf t r Θ) : h.tauX * h.tauX = 1 := by
  rw [FyConf.tauX, ← map_mul]
  have : ((DihedralGroup.r 2 : DihedralGroup 4), (1 : Z3), (1 : Equiv.Perm (Fin 5))) *
      (DihedralGroup.r 2, 1, 1) = 1 := by decide
  rw [this, map_one]

theorem FyConf.tauX_ne_one (h : FyConf t r Θ) : h.tauX ≠ 1 := by
  intro h1
  exact d8_r2_ne_one ((h.Phi_eq_one_iff _).1 h1).1

theorem FyConf.Phi_comm_iff (h : FyConf t r Θ) (m m' : HModel) :
    h.Phi m * h.Phi m' = h.Phi m' * h.Phi m ↔
      m.1 * m'.1 = m'.1 * m.1 ∧ m.2.2 * m'.2.2 = m'.2.2 * m.2.2 := by
  rw [← map_mul, ← map_mul, ← inv_mul_eq_one, ← map_inv, ← map_mul, h.Phi_eq_one_iff]
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, inv_mul_eq_one]

theorem FyConf.exists_lift (h : FyConf t r Θ) (x : RedX r)
    (hx : x * h.tauX = h.tauX * x) : ∃ m : HModel, h.Phi m = x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  set T : RedC r := h.thetaC (DihedralGroup.r 2, 1, 1) with hT
  have hTT : T * T = 1 := by
    rw [hT, ← map_mul]
    have : ((DihedralGroup.r 2 : DihedralGroup 4), (1 : Z3), (1 : Equiv.Perm (Fin 5))) *
        (DihedralGroup.r 2, 1, 1) = 1 := by decide
    rw [this, map_one]
  have hxO : y⁻¹ * (T * y * T⁻¹) ∈ RedO r := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 : (QuotientGroup.mk T : RedX r) * QuotientGroup.mk y =
        QuotientGroup.mk y * QuotientGroup.mk T := hx.symm
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h1]
    group
  obtain ⟨c, hc, hyc⟩ := exists_fixed_in_coset (O := RedO r) (redO_odd r) hTT hxO
  have hct : (c : G) * t = t * (c : G) := by
    have := congrArg Subtype.val hc
    have h2 : (T : G) = t := h.t_eq
    simp only [Subgroup.coe_mul] at this
    rw [h2] at this
    exact this.symm
  have hcr : (c : G) * r = r * (c : G) := mem_centralizer_singleton_iff.1 c.2
  obtain ⟨m, hm⟩ := (h.mem_range _).1 ⟨hct, hcr⟩
  refine ⟨m, ?_⟩
  have hmc : h.thetaC m = c := Subtype.ext hm
  rw [FyConf.Phi_apply, hmc]
  exact (QuotientGroup.eq.2 hyc).symm

theorem FyConf.Phi_comm_tau (h : FyConf t r Θ) (m : HModel) :
    h.Phi m * h.tauX = h.tauX * h.Phi m := by
  rw [FyConf.tauX, h.Phi_comm_iff]
  refine ⟨?_, by simp⟩
  show m.1 * DihedralGroup.r 2 = DihedralGroup.r 2 * m.1
  revert m
  intro m
  obtain ⟨d, c, σ⟩ := m
  show d * DihedralGroup.r 2 = DihedralGroup.r 2 * d
  revert d
  decide

theorem FyConf.cent_eq_range (h : FyConf t r Θ) :
    centralizer ({h.tauX} : Set (RedX r)) = h.Phi.range := by
  ext x
  constructor
  · intro hx
    obtain ⟨m, hm⟩ := h.exists_lift x (mem_centralizer_singleton_iff.1 hx)
    exact ⟨m, hm⟩
  · rintro ⟨m, rfl⟩
    exact mem_centralizer_singleton_iff.2 (h.Phi_comm_tau m)

theorem FyConf.card_ker_Phi (h : FyConf t r Θ) : Nat.card h.Phi.ker = 3 := by
  have hmem : ∀ c : Z3, (1, c, 1) ∈ h.Phi.ker := fun c => by
    rw [MonoidHom.mem_ker, h.Phi_eq_one_iff]; exact ⟨rfl, rfl⟩
  let e : Z3 → h.Phi.ker := fun c => ⟨(1, c, 1), hmem c⟩
  have hbij : Function.Bijective e := by
    constructor
    · intro a b hab
      have := congrArg (fun x : h.Phi.ker => (x : HModel).2.1) hab
      exact this
    · rintro ⟨⟨d, c, σ⟩, hm⟩
      rw [MonoidHom.mem_ker, h.Phi_eq_one_iff] at hm
      obtain ⟨h1, h2⟩ := hm
      simp only at h1 h2
      subst h1; subst h2
      exact ⟨c, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective e hbij)]
  rw [Nat.card_eq_fintype_card]; decide

theorem FyConf.card_cent (h : FyConf t r Θ) :
    Nat.card (centralizer ({h.tauX} : Set (RedX r))) = 960 := by
  rw [h.cent_eq_range]
  have h1 := Subgroup.card_ker_mul_card_range h.Phi
  rw [h.card_ker_Phi, card_hmodel] at h1
  omega

end CFSG.EvenSporadicStandard.TwoHS
