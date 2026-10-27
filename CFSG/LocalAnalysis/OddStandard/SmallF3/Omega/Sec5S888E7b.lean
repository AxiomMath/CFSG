module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E7a

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

private theorem s888_exists_mem_normalizer_not_mem [Finite X] {p : ℕ} [Fact p.Prime]
    {P Q : Subgroup X} (hQ : IsPGroup p Q) (hlt : P < Q) :
    ∃ x ∈ Q, x ∉ P ∧ x ∈ normalizer (P : Set X) := by
  haveI : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt' : P.subgroupOf Q < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hlt.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : Q) ∈ P.subgroupOf Q := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt')
  refine ⟨y, y.2, fun h => hyP (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (normalizer (P : Set X)).subgroupOf Q := by
    rw [Subgroup.subgroupOf_normalizer_eq hlt.le]
    exact hyN
  exact Subgroup.mem_subgroupOf.mp hy

private theorem s888_map_conj_comm {g : X} {D : Subgroup X}
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) :
    ∀ a ∈ D.map (MulAut.conj g).toMonoidHom,
      ∀ b ∈ D.map (MulAut.conj g).toMonoidHom, a * b = b * a := by
  intro a ha b hb
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hb
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc (g * v * g⁻¹) * (g * w * g⁻¹)
      = g * (v * w) * g⁻¹ := by group
    _ = g * (w * v) * g⁻¹ := by rw [hcomm v hv w hw]
    _ = (g * w * g⁻¹) * (g * v * g⁻¹) := by group

private theorem s888_map_conj_sq {g : X} {D : Subgroup X}
    (hsq : ∀ a ∈ D, a * a = 1) :
    ∀ a ∈ D.map (MulAut.conj g).toMonoidHom, a * a = 1 := by
  intro a ha
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp ha
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc (g * v * g⁻¹) * (g * v * g⁻¹)
      = g * (v * v) * g⁻¹ := by group
    _ = g * 1 * g⁻¹ := by rw [hsq v hv]
    _ = 1 := by group

theorem isSylow2Of_top [Finite X] (hS : PlaneSys V W) (hpar : PlaneParity V W)
    (hC : ∀ y ∈ normalizer (V : Set X), y * y = 1 → y ∈ centralizer (V : Set X) → y ∈ V)
    {T : Subgroup X} (hVT : V ≤ T) (hT : IsSylow2Of T (normalizer (V : Set X))) :
    IsSylow2Of T (⊤ : Subgroup X) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTN, hTp, hTodd⟩ := hT
  obtain ⟨S₀, hTS₀⟩ := hTp.exists_le_sylow
  have hS₀p : IsPGroup 2 ↥(S₀ : Subgroup X) := S₀.isPGroup'
  have hT_eq : T = S₀ := by
    by_contra hne
    have hlt : T < S₀ := lt_of_le_of_ne hTS₀ hne
    obtain ⟨g, hgS₀, hgT, hgNormT⟩ := s888_exists_mem_normalizer_not_mem S₀.isPGroup' hlt
    have hE_le_T : V.map (MulAut.conj g).toMonoidHom ≤ T := by
      calc V.map (MulAut.conj g).toMonoidHom ≤ T.map (MulAut.conj g).toMonoidHom :=
            Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hVT
        _ = T := by
              have h := (Subgroup.mem_normalizer_iff_map_conj_eq (H := T) (g := g)).mp hgNormT
              simpa [MulEquiv.coe_toMonoidHom] using h
    have hE_N : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set X) :=
      le_trans hE_le_T hTN
    have hEc : ∀ a ∈ V.map (MulAut.conj g).toMonoidHom,
        ∀ b ∈ V.map (MulAut.conj g).toMonoidHom, a * b = b * a :=
      s888_map_conj_comm hS.comm
    have hEs : ∀ a ∈ V.map (MulAut.conj g).toMonoidHom, a * a = 1 :=
      s888_map_conj_sq hS.sq
    have hcardE : 2 ^ 8 ≤ Nat.card (V.map (MulAut.conj g).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective, hS.card_D]
    have hEeq : V.map (MulAut.conj g).toMonoidHom = V :=
      eq_of_card_le hS hpar hC hE_N hEc hEs hcardE
    have hgN : g ∈ normalizer (V : Set X) := by
      apply (Subgroup.mem_normalizer_iff_map_conj_eq (H := V) (g := g)).mpr
      simpa [MulEquiv.coe_toMonoidHom] using hEeq
    have hT'_le_S₀ : T ⊔ Subgroup.zpowers g ≤ S₀ :=
      sup_le hTS₀ (Subgroup.zpowers_le.mpr hgS₀)
    have hT'_N : T ⊔ Subgroup.zpowers g ≤ normalizer (V : Set X) :=
      sup_le hTN (Subgroup.zpowers_le.mpr hgN)
    have hT'p : IsPGroup 2 ↥(T ⊔ Subgroup.zpowers g : Subgroup X) :=
      (hS₀p.to_subgroup ((T ⊔ Subgroup.zpowers g).subgroupOf S₀)).of_equiv
        (Subgroup.subgroupOfEquivOfLe hT'_le_S₀)
    have hT'idx : ∃ n : ℕ, T.relIndex (T ⊔ Subgroup.zpowers g) = 2 ^ n := by
      obtain ⟨n, hn⟩ := hT'p.index (T.subgroupOf (T ⊔ Subgroup.zpowers g))
      exact ⟨n, hn⟩
    have hrel : T.relIndex (T ⊔ Subgroup.zpowers g) *
        (T ⊔ Subgroup.zpowers g).relIndex (normalizer (V : Set X)) =
        T.relIndex (normalizer (V : Set X)) :=
      Subgroup.relIndex_mul_relIndex (H := T) (K := T ⊔ Subgroup.zpowers g)
        (L := normalizer (V : Set X)) le_sup_left hT'_N
    have hodd : ¬ 2 ∣ T.relIndex (T ⊔ Subgroup.zpowers g) := by
      intro hdvd
      exact hTodd (hrel ▸ dvd_mul_of_dvd_left hdvd _)
    have hrel1 : T.relIndex (T ⊔ Subgroup.zpowers g) = 1 := by
      obtain ⟨n, hn⟩ := hT'idx
      rcases n with _ | k
      · simpa using hn
      · exact absurd (hn.symm ▸ dvd_pow_self 2 (Nat.succ_ne_zero k)) hodd
    have hle : T ⊔ Subgroup.zpowers g ≤ T := Subgroup.relIndex_eq_one.mp hrel1
    exact hgT (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers g)))
  refine ⟨le_top, hTp, ?_⟩
  rw [Subgroup.relIndex_top_right, hT_eq]
  exact S₀.not_dvd_index

end CFSG.OddStandard.SmallF3.Omega
