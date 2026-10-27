module

public import CFSG.CGT.PushingUpLit.T2K.SixB
public import CFSG.CGT.PushingUpLit.T2KR.Star
public import CFSG.CGT.Timmesfeld75.WeaklyClosed

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ} {D : Subgroup G} {g : G}

theorem mem_of_conjSubgroup_le (hs : Sec6 G L M T n) {h : G}
    (hle : conjSubgroup h (QOf L M) ≤ M) : h ∈ M := by
  have hQ2 : IsPGroup 2 (conjSubgroup h (QOf L M)) :=
    isPGroup_two_of_isElemAbelian (isElemAbelian_map_conj hs.Q_abelian h)
  obtain ⟨k, hkM, hk⟩ := exists_conj_le_of_isPGroup hs.sec4.sylow hQ2 hle
  have h1 : conjSubgroup (k * h) (QOf L M) ≤ T := by
    rw [← conjSubgroup_conjSubgroup]
    exact hk
  have h2 := hs.Q_wc (k * h) h1
  have h3 : k * h ∈ M := by
    rw [← hs.N_Q]
    exact mem_normalizer_of_map_conj_eq h2
  have : h = k⁻¹ * (k * h) := by group
  rw [this]
  exact M.mul_mem (M.inv_mem hkM) h3

theorem corBHyp_star (hs : Sit64 G L M T n D g) : CorBHyp (star D (QOf L M)) := by
  have hDQ : D ≤ QOf L M := hs.D_lt_Q.le
  have hQH : QOf L M ≤ Hc D := fun q hq => Subgroup.mem_centralizer_iff.2 fun d hd =>
    elemAbelian_mul_comm hs.sec6.Q_abelian (hDQ hd) hq
  have hQA := isElemAbelian_star (D := D) hs.sec6.Q_abelian
  refine ⟨hQA, ?_, ?_⟩
  ·
    intro ĥ
    obtain ⟨h, rfl⟩ := pi_surjective D ĥ
    have hDc := D_le_conjSubgroup hDQ h
    rw [star_conj hDQ h, ← star_inf hDQ hDc]
    by_cases hM : (h : G) ∈ M
    · right
      have : conjSubgroup (h : G) (QOf L M) = QOf L M :=
        map_conj_eq_of_mem_normalizer (by rw [hs.sec6.N_Q]; exact hM)
      rw [this, inf_idem]
    · left
      have := hs.ti (h : G) h.2 hM
      rw [show conjSubgroup (h : G) (QOf L M) = (QOf L M).map (MulAut.conj (h : G)).toMonoidHom
        from rfl, this, star_self]
  ·
    intro ĥ
    obtain ⟨h, rfl⟩ := pi_surjective D ĥ
    have hDc := D_le_conjSubgroup hDQ h
    rw [star_conj hDQ h]
    constructor
    · intro hcomm
      have key : ∀ y ∈ conjSubgroup (h : G) (QOf L M), ∀ x ∈ QOf L M,
          y * x * y⁻¹ ∈ QOf L M := by
        intro y hy x hx
        have hyH : y ∈ Hc D := by
          obtain ⟨q, hq, rfl⟩ := hy
          exact conj_mem_Hc h.2 (hQH hq)
        have h1 : pi D ⟨x, hQH hx⟩ * pi D ⟨y, hyH⟩ = pi D ⟨y, hyH⟩ * pi D ⟨x, hQH hx⟩ :=
          hcomm (pi D ⟨x, hQH hx⟩) ((mem_star_iff hDQ _).2 hx) (pi D ⟨y, hyH⟩)
            ((mem_star_iff hDc _).2 hy)
        rw [← map_mul, ← map_mul] at h1
        have h3 := (pi_eq_pi_iff D).1 h1
        have hd : ((x * y)⁻¹ * (y * x) : G) ∈ D := h3
        have hyd : y * ((x * y)⁻¹ * (y * x)) = ((x * y)⁻¹ * (y * x)) * y :=
          (Subgroup.mem_centralizer_iff.1 hyH _ hd).symm
        have e : y * x * y⁻¹ = x * ((x * y)⁻¹ * (y * x)) := by
          have h4 : y * x = x * y * ((x * y)⁻¹ * (y * x)) := by group
          calc y * x * y⁻¹ = (x * y * ((x * y)⁻¹ * (y * x))) * y⁻¹ := by rw [← h4]
            _ = x * (y * ((x * y)⁻¹ * (y * x)) * y⁻¹) := by group
            _ = x * (((x * y)⁻¹ * (y * x)) * y * y⁻¹) := by rw [hyd]
            _ = x * ((x * y)⁻¹ * (y * x)) := by group
        rw [e]
        exact (QOf L M).mul_mem hx (hDQ hd)
      have hy : conjSubgroup (h : G) (QOf L M) ≤ M := by
        intro y hy
        have hN : y ∈ Subgroup.normalizer ((QOf L M : Subgroup G) : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro x
          refine ⟨fun hx => key y hy x hx, fun hx => ?_⟩
          have := key y⁻¹ ((conjSubgroup (h : G) (QOf L M)).inv_mem hy) _ hx
          simpa [mul_assoc] using this
        rw [← hs.sec6.N_Q]
        exact hN
      have hhM := mem_of_conjSubgroup_le hs.sec6 hy
      have : conjSubgroup (h : G) (QOf L M) = QOf L M :=
        map_conj_eq_of_mem_normalizer (by rw [hs.sec6.N_Q]; exact hhM)
      rw [this]
    · intro heq x hx y hy
      rw [heq] at hy
      exact congrArg Subtype.val (hQA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem isWC_star (hs : Sit64 G L M T n D g) : IsWC (star D (QOf L M)) :=
  isWC_of_corBHyp (corBHyp_star hs)

end CFSG.CGT.PushingUpLit.T2KR
