module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Card
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4JF
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Nrm
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31SylConj

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private theorem natCard_orbit_mul_card_stabilizer' {Γ α : Type} [Group Γ] [MulAction Γ α]
    (b : α) :
    Nat.card (MulAction.orbit Γ b) * Nat.card (MulAction.stabilizer Γ b) = Nat.card Γ := by
  rw [← Nat.card_prod (MulAction.orbit Γ b) (MulAction.stabilizer Γ b)]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Γ b)

private theorem comm_t_of_mem_H {s : Setting3 G L} {x : G} (hx : x ∈ s.H) :
    x * s.t = s.t * x :=
  Subgroup.mem_centralizer_singleton_iff.mp hx

private theorem le_f4X_of_le_normalizer {s : Setting3 G L} {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (s.fr.F : Set G)) (hAH : A ≤ s.H) : A ≤ f4X s := by
  intro x hx
  rw [f4X, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, MonoidHom.map_zpowers]
  have hFmap : (s.fr.F).map (MulAut.conj x) = s.fr.F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAN hx)
  have hcomm : x * s.t = s.t * x := comm_t_of_mem_H (hAH hx)
  have hconj : (↑(MulAut.conj x) : G →* G) s.t = s.t := by
    change (MulAut.conj x) s.t = s.t
    rw [MulAut.conj_apply, hcomm]; group
  rw [hconj, hFmap]

theorem y4_f4X_le_H (c : Ctx4 s e) (h42 : IsSylowIn 2 (⊤ : Subgroup G) s.T₂) :
    f4X s ≤ s.H := by
  classical
  letI : MulAction ↥(f4X s) G :=
    MulAction.compHom G ((MulAut.conj).comp (f4X s).subtype)
  have hsmul : ∀ (l : ↥(f4X s)) (x : G), l • x = (l : G) * x * (l : G)⁻¹ := fun _ _ => rfl
  by_contra hle
  obtain ⟨x₀, hx₀X, hx₀H⟩ := SetLike.not_le_iff_exists.mp hle
  have htt : s.t * s.t = 1 := by
    rw [← pow_two, ← s.t_order]
    exact pow_orderOf_eq_one s.t
  let f₀ : ↥s.fr.F := ⟨x₀ * s.t * x₀⁻¹ * s.t, by
    obtain ⟨v, hv, hveq⟩ := y54_tX_sub c.toF33 x₀ hx₀X
    rw [hveq, mul_assoc, htt, mul_one]
    exact hv⟩
  have hf₀_ne : (f₀ : G) ≠ 1 := by
    intro h
    have h1 : x₀ * s.t * x₀⁻¹ * s.t = 1 := h
    have hconj : x₀ * s.t * x₀⁻¹ = s.t := by
      calc x₀ * s.t * x₀⁻¹ = (x₀ * s.t * x₀⁻¹) * (s.t * s.t) := by rw [htt, mul_one]
        _ = ((x₀ * s.t * x₀⁻¹) * s.t) * s.t := by group
        _ = 1 * s.t := by rw [h1]
        _ = s.t := one_mul _
    have h2 : x₀ * s.t = s.t * x₀ := by
      calc x₀ * s.t = (x₀ * s.t * x₀⁻¹) * x₀ := by group
        _ = s.t * x₀ := by rw [hconj]
    exact hx₀H (Subgroup.mem_centralizer_singleton_iff.mpr h2)
  have hv_orbit : ∀ v : ↥s.fr.F, (v : G) * s.t ∈ MulAction.orbit ↥(f4X s) s.t := by
    intro v
    by_cases hv1 : (v : G) = 1
    · refine MulAction.mem_orbit_iff.mpr ⟨1, ?_⟩
      rw [hsmul]
      simp [hv1]
    · obtain ⟨n, hn, hnconj⟩ := y54_trans1 c.toF33 (f₀ : G) f₀.2 (v : G) v.2 hf₀_ne hv1
      have hnX : n ∈ f4X s := (y54_NL_le_N c.toF33).trans (y54_N_le_X c.toF33) hn
      have hnH : n ∈ s.H := (Subgroup.mem_inf.mp (y54_NL_le_N c.toF33 hn)).1
      have hnt : n * s.t = s.t * n := comm_t_of_mem_H hnH
      refine MulAction.mem_orbit_iff.mpr
        ⟨⟨n * x₀, (f4X s).mul_mem hnX hx₀X⟩, ?_⟩
      rw [hsmul]
      have hx₀conj : x₀ * s.t * x₀⁻¹ = (f₀ : G) * s.t := by
        rw [show (f₀ : G) = x₀ * s.t * x₀⁻¹ * s.t from rfl]
        conv_rhs => rw [mul_assoc, htt, mul_one]
      calc (n * x₀) * s.t * (n * x₀)⁻¹
          = n * (x₀ * s.t * x₀⁻¹) * n⁻¹ := by group
        _ = n * ((f₀ : G) * s.t) * n⁻¹ := by rw [hx₀conj]
        _ = (n * (f₀ : G) * n⁻¹) * (n * s.t * n⁻¹) := by group
        _ = (v : G) * s.t := by rw [hnconj, hnt]; group
  have hbij : Function.Bijective (fun v : ↥s.fr.F =>
      (⟨(v : G) * s.t, hv_orbit v⟩ : MulAction.orbit ↥(f4X s) s.t)) := by
    constructor
    · intro v w hvw
      apply Subtype.ext
      exact mul_right_cancel (congrArg Subtype.val hvw)
    · intro u
      obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp u.2
      obtain ⟨v, hv, hveq⟩ := y54_tX_sub c.toF33 (x : G) x.2
      have hu : u.1 = v * s.t := by rw [← hx, hsmul x s.t, hveq]
      exact ⟨⟨v, hv⟩, Subtype.ext (by rw [hu])⟩
  have hFcard : Nat.card ↥s.fr.F = 8 := by
    simpa using (y54_F_isE3 c.toF33).2
  have horb_card : Nat.card (MulAction.orbit ↥(f4X s) s.t) = 8 := by
    have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
    rw [← hcard, hFcard]
  have hstab : MulAction.stabilizer ↥(f4X s) s.t =
      (f4X s ⊓ s.H).subgroupOf (f4X s) := by
    ext l
    simp only [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨l.2, ?_⟩
      have h2 : (l : G) * s.t = s.t * (l : G) := by
        calc (l : G) * s.t = ((l : G) * s.t * (l : G)⁻¹) * (l : G) := by group
          _ = s.t * (l : G) := by rw [h]
      exact Subgroup.mem_centralizer_singleton_iff.mpr h2
    · rintro ⟨-, h⟩
      have hh : (l : G) * s.t = s.t * (l : G) := comm_t_of_mem_H h
      calc (l : G) * s.t * (l : G)⁻¹ = s.t * (l : G) * (l : G)⁻¹ := by rw [hh]
        _ = s.t := by group
  have hstab_card : Nat.card (MulAction.stabilizer ↥(f4X s) s.t) =
      Nat.card ↥(f4X s ⊓ s.H) := by
    rw [hstab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hXcard : Nat.card ↥(f4X s) = 8 * Nat.card ↥(f4X s ⊓ s.H) := by
    have hOS := natCard_orbit_mul_card_stabilizer' (Γ := ↥(f4X s)) s.t
    rw [horb_card, hstab_card] at hOS
    exact hOS.symm
  have hXHpos : 0 < Nat.card ↥(f4X s ⊓ s.H) := by
    have : Nonempty ↥(f4X s ⊓ s.H) := ⟨⟨1, (f4X s ⊓ s.H).one_mem⟩⟩
    exact Nat.card_pos
  have hXHrel : (f4X s ⊓ s.H).relIndex (f4X s) = 8 := by
    have h := Subgroup.relIndex_mul_card (H := f4X s ⊓ s.H) (K := f4X s)
    rw [inf_of_le_left inf_le_left, hXcard] at h
    exact Nat.mul_right_cancel hXHpos h
  have hT_le_X : s.T ≤ f4X s :=
    le_f4X_of_le_normalizer (y4_T_normF c.toF33) s.sylow_T.1
  have hT_le_H : s.T ≤ s.H := s.sylow_T.1
  have hT_le_inf : s.T ≤ f4X s ⊓ s.H := le_inf hT_le_X hT_le_H
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT'pg : IsPGroup 2 (s.T.subgroupOf (f4X s)) := s.sylow_T.2.1.comap_subtype
  obtain ⟨Q', hT'Q'⟩ := hT'pg.exists_le_sylow
  set Q : Subgroup G := (Q' : Subgroup ↥(f4X s)).map (f4X s).subtype with hQ
  have hQ_le_X : Q ≤ f4X s := by rw [hQ]; exact Subgroup.map_subtype_le _
  have hQpg : IsPGroup 2 Q := by rw [hQ]; exact Q'.isPGroup'.map (f4X s).subtype
  have hT_le_Q : s.T ≤ Q := by
    rw [hQ]
    intro t ht
    exact Subgroup.mem_map.mpr ⟨⟨t, hT_le_X ht⟩,
      hT'Q' (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  have hQ_sylow : IsSylowIn 2 (f4X s) Q := by
    rw [hQ]
    refine ⟨Subgroup.map_subtype_le _, Q'.isPGroup'.map (f4X s).subtype, ?_⟩
    have h := Subgroup.relIndex_map_map_of_injective (f := (f4X s).subtype)
      (Q' : Subgroup ↥(f4X s)) (⊤ : Subgroup ↥(f4X s)) (f4X s).subtype_injective
    rw [Subgroup.map_top (f4X s).subtype, Subgroup.range_subtype,
      Subgroup.relIndex_top_right] at h
    rw [h]
    exact Q'.not_dvd_index
  have hXrel : s.T.relIndex (f4X s) =
      s.T.relIndex (f4X s ⊓ s.H) * (f4X s ⊓ s.H).relIndex (f4X s) :=
    (Subgroup.relIndex_mul_relIndex (H := s.T) (K := f4X s ⊓ s.H) (L := f4X s)
      hT_le_inf inf_le_left).symm
  have hrelTQ : s.T.relIndex Q * Q.relIndex (f4X s) = s.T.relIndex (f4X s) :=
    Subgroup.relIndex_mul_relIndex (H := s.T) (K := Q) (L := f4X s) hT_le_Q hQ_le_X
  have h8dvd : 8 ∣ Q.relIndex (f4X s) * s.T.relIndex Q := by
    refine ⟨s.T.relIndex (f4X s ⊓ s.H), ?_⟩
    rw [mul_comm (Q.relIndex (f4X s)), hrelTQ, hXrel, hXHrel]
    ring
  have hQodd : Nat.Coprime 8 (Q.relIndex (f4X s)) := by
    have h2 : ¬ 2 ∣ Q.relIndex (f4X s) := hQ_sylow.2.2
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr h2).pow_left 3
  have h8TQ : 8 ∣ s.T.relIndex Q := hQodd.dvd_of_dvd_mul_left h8dvd
  have hTQne : s.T.relIndex Q ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card (H := s.T) (K := Q)
    rw [inf_of_le_left hT_le_Q, h0, zero_mul] at h
    have hpos : 0 < Nat.card ↥Q := by
      have : Nonempty ↥Q := ⟨⟨1, Q.one_mem⟩⟩
      exact Nat.card_pos
    exact hpos.ne' h.symm
  have h8le : 8 ≤ s.T.relIndex Q := Nat.le_of_dvd (Nat.pos_of_ne_zero hTQne) h8TQ
  have hTpos : 0 < Nat.card ↥s.T := by
    have : Nonempty ↥s.T := ⟨⟨1, s.T.one_mem⟩⟩
    exact Nat.card_pos
  have hQrel : s.T.relIndex Q * Nat.card ↥s.T = Nat.card ↥Q := by
    have h := Subgroup.relIndex_mul_card (H := s.T) (K := Q)
    rwa [inf_of_le_left hT_le_Q] at h
  have hQcard_ge : 8 * Nat.card ↥s.T ≤ Nat.card ↥Q := by
    rw [← hQrel]
    exact Nat.mul_le_mul_right _ h8le
  have hQcard_le : Nat.card ↥Q ≤ Nat.card ↥s.T₂ := by
    obtain ⟨h, -, hconj⟩ :=
      exists_conj_le_isSylowIn (V := ⊤) (P := s.T₂) (Q := Q) h42 hQpg le_top
    have hcardconj : Nat.card ↥(conjSub h Q) = Nat.card ↥Q := by
      simpa only [conjSub] using Subgroup.card_map_of_injective
        (f := (MulAut.conj h).toMonoidHom) (K := Q) (MulAut.conj h).injective
    rw [← hcardconj]
    exact Subgroup.card_le_of_le hconj
  rw [y4_card_T2 c.toF33] at hQcard_le
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
