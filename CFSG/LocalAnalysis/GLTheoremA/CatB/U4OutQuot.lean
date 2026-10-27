module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] noncomputable def u4AutQuot (Q : Type) [Group Q] (v : MulAut Q) :
    MulAut (Q ⧸ Subgroup.center Q) :=
  QuotientGroup.congr (Subgroup.center Q) (Subgroup.center Q) v (Subgroup.map_center_eq v)

theorem u4AutQuot_mk {Q : Type} [Group Q] (v : MulAut Q) (g : Q) :
    u4AutQuot Q v (QuotientGroup.mk g) = QuotientGroup.mk (v g) :=
  QuotientGroup.congr_mk _ _ _ _ g

@[expose] noncomputable def u4AutQuotHom (Q : Type) [Group Q] :
    MulAut Q →* MulAut (Q ⧸ Subgroup.center Q) where
  toFun := u4AutQuot Q
  map_one' := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact u4AutQuot_mk 1 g
  map_mul' v w := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    show u4AutQuot Q (v * w) (QuotientGroup.mk g) =
      u4AutQuot Q v (u4AutQuot Q w (QuotientGroup.mk g))
    rw [u4AutQuot_mk, u4AutQuot_mk, u4AutQuot_mk]
    rfl

theorem u4AutQuot_conj {Q : Type} [Group Q] (g : Q) :
    u4AutQuot Q (MulAut.conj g) = MulAut.conj (QuotientGroup.mk g : Q ⧸ Subgroup.center Q) := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  simp [u4AutQuot_mk, MulAut.conj_apply]

theorem u4Out_mem_innerAut_of_autQuot {Q : Type} [Group Q] (hperf : commutator Q = ⊤) {v : MulAut Q}
    (hv : u4AutQuotHom Q v ∈ innerAut (Q ⧸ Subgroup.center Q)) : v ∈ innerAut Q := by
  obtain ⟨p, hp⟩ := hv
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
  show v ∈ (MulAut.conj : Q →* MulAut Q).range
  refine MonoidHom.mem_range.2 ⟨g, mulAut_quot_injective hperf ?_⟩
  show u4AutQuot Q (MulAut.conj g) = u4AutQuot Q v
  rw [u4AutQuot_conj]
  exact hp

theorem u4Out_index_dvd_quot {Q : Type} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    (innerAut Q).index ∣ (innerAut (Q ⧸ Subgroup.center Q)).index := by
  have hperf : commutator Q = ⊤ := hQ.1
  have hle : innerAut Q ≤ (innerAut (Q ⧸ Subgroup.center Q)).comap (u4AutQuotHom Q) := by
    rintro _ ⟨g, rfl⟩
    show u4AutQuot Q (MulAut.conj g) ∈ (MulAut.conj : Q ⧸ Subgroup.center Q →* _).range
    rw [u4AutQuot_conj]
    exact MonoidHom.mem_range.2 ⟨_, rfl⟩
  have hφ : Function.Injective (QuotientGroup.map (innerAut Q) (innerAut (Q ⧸ Subgroup.center Q))
      (u4AutQuotHom Q) hle) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
    rw [QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at hx
    exact (QuotientGroup.eq_one_iff v).2 (u4Out_mem_innerAut_of_autQuot hperf hx)
  calc (innerAut Q).index = Nat.card (MulAut Q ⧸ innerAut Q) := rfl
    _ = Nat.card (MonoidHom.range (QuotientGroup.map (innerAut Q)
          (innerAut (Q ⧸ Subgroup.center Q)) (u4AutQuotHom Q) hle)) :=
        Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
    _ ∣ Nat.card (MulAut (Q ⧸ Subgroup.center Q) ⧸ innerAut (Q ⧸ Subgroup.center Q)) :=
        Subgroup.card_subgroup_dvd_card _
    _ = (innerAut (Q ⧸ Subgroup.center Q)).index := rfl

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
