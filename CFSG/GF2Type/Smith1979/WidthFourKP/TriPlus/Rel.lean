module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.AtT
public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.Perm3
public import CFSG.GF2Type.Smith1980Orth.S2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.TriPlus

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S7

variable {G : Type} [Group G] [Finite G]

namespace TriData

variable {S : Setting G} {g : G} (T : TriData S g)

theorem s2Rel_cent_le (i0 : Fin 3) :
    ∀ x ∈ S.Mbar, x * T.l i0 = T.l i0 * x →
      x ∈ S.Mbar ⊓ normalizer (zpowers (eb T.σ i0) : Set S.O) := by
  intro x hx hcomm
  have hpi : T.perm ⟨x, hx⟩ i0 = i0 :=
    T.perm_eq_of_commute (x := ⟨x, hx⟩) (i := i0) (by simpa using hcomm)
  exact ⟨hx, (T.mem_normalizer_iff ⟨x, hx⟩ i0).mpr hpi⟩

theorem s2Rel_orbit (H : Hyp4 S g) (i0 : Fin 3) :
    ∀ x ∈ S.Mbar, ∃ y ∈ S.Mbar ⊓ normalizer (zpowers (eb T.σ i0) : Set S.O),
      ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
  classical
  intro x hx
  obtain ⟨c, hc⟩ := T.conj_l ⟨x, hx⟩
  let y : S.O := T.σ (Multiplicative.ofAdd c)
  have hyY : y ∈ S7.Obar S := T.basis.mem_iff.mpr ⟨c, rfl⟩
  have hyM : y ∈ S.Mbar := S7.Obar_le_Mbar hyY
  have hyk : y * eb T.σ i0 = eb T.σ i0 * y :=
    T.basis.comm hyY (T.basis.eb_mem i0)
  have hynorm : y ∈ normalizer (zpowers (eb T.σ i0) : Set S.O) := by
    have hyC : y ∈ centralizer (zpowers (eb T.σ i0) : Set S.O) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh
      rw [← hn]
      exact (Commute.zpow_right hyk n).symm
    exact Subgroup.centralizer_le_normalizer _ hyC
  have hL : S.Lbar g = Subgroup.closure (Set.range T.l) := by
    refine le_antisymm T.basis.gen ((Subgroup.closure_le (S.Lbar g)).mpr ?_)
    rintro _ ⟨i, rfl⟩
    exact T.basis.l_mem i
  let z : S.O := y⁻¹ * x
  have hnorm : z ∈ normalizer (S.Lbar g : Set S.O) := by
    refine S4.mem_normalizer_of_conj_le (X := S.O) (P := S.Lbar g) (y := z) ?_
    intro l hl
    rw [hL] at hl ⊢
    induction hl using Subgroup.closure_induction with
    | mem l hl =>
        obtain ⟨i, rfl⟩ := hl
        have hconji : z * T.l i * z⁻¹ = T.l (T.perm ⟨x, hx⟩ i) := by
          have hgroup : z * T.l i * z⁻¹ =
              y⁻¹ * ((x : S.O) * T.l i * (x : S.O)⁻¹) * y := by
            dsimp only [z]
            group
          rw [hgroup, hc i]
          dsimp only [y]
          group
        rw [hconji]
        exact Subgroup.subset_closure ⟨T.perm ⟨x, hx⟩ i, rfl⟩
    | one => simpa using (Subgroup.closure (Set.range T.l)).one_mem
    | mul a b ha hb iha ihb =>
        have h : z * (a * b) * z⁻¹ =
            (z * a * z⁻¹) * (z * b * z⁻¹) := by group
        rw [h]
        exact (Subgroup.closure (Set.range T.l)).mul_mem iha ihb
    | inv a ha iha =>
        have h : z * a⁻¹ * z⁻¹ = (z * a * z⁻¹)⁻¹ := by group
        rw [h]
        exact (Subgroup.closure (Set.range T.l)).inv_mem iha
  have hfix : ((y⁻¹ * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
    S4.fix_of_mem_normalizer H hnorm
  have hfix' : ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) =
      S.cl (g * S.z * g⁻¹) := by
    simpa [Subgroup.coe_mul, LinearEquiv.mul_apply] using hfix
  have hxy : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
    calc ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))
        = ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
              (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
                (S.cl (g * S.z * g⁻¹)))) :=
          (S4.apply_inv_apply_O y _).symm
      _ = ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
          rw [hfix']
  exact ⟨y, ⟨hyM, hynorm⟩, hxy⟩

theorem s2Rel_inv_conj (i0 : Fin 3)
    (htrans : ∀ k : Fin 3, ∃ x : S.Mbar, T.perm x k ≠ k) :
    ∀ y ∈ S.Mbar, y * y = 1 → ∃ m ∈ S.Mbar,
      m * y * m⁻¹ ∈ S.Mbar ⊓ normalizer (zpowers (eb T.σ i0) : Set S.O) := by
  intro y hy hy2
  have hy2' : (⟨y, hy⟩ : S.Mbar) * ⟨y, hy⟩ = 1 := Subtype.ext (by simpa using hy2)
  obtain ⟨j, hj⟩ := perm3_exists_fixed (x := T.perm ⟨y, hy⟩)
    (by rw [← map_mul, hy2', map_one])
  have htrans' : ∀ k : Fin 3, ∃ x ∈ T.perm.range, x k ≠ k := by
    intro kk
    obtain ⟨x, hx⟩ := htrans kk
    exact ⟨T.perm x, ⟨x, rfl⟩, hx⟩
  obtain ⟨p, hp, hpj⟩ := perm3_exists_apply_eq htrans' j i0
  obtain ⟨m, rfl⟩ := hp
  refine ⟨(m : S.O), m.2, ?_⟩
  have hperm : T.perm (m * ⟨y, hy⟩ * m⁻¹) i0 = i0 := by
    have hmj' : (T.perm m)⁻¹ i0 = j :=
      (Equiv.symm_apply_eq (T.perm m)).mpr hpj.symm
    calc T.perm (m * ⟨y, hy⟩ * m⁻¹) i0
        = (T.perm m * T.perm ⟨y, hy⟩ * (T.perm m)⁻¹) i0 := by
            rw [map_mul, map_mul, map_inv]
      _ = (T.perm m) ((T.perm ⟨y, hy⟩) ((T.perm m)⁻¹ i0)) := by
            rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      _ = (T.perm m) ((T.perm ⟨y, hy⟩) j) := by rw [hmj']
      _ = (T.perm m) j := congrArg (T.perm m) hj
      _ = i0 := hpj
  have hxM : (m : S.O) * y * (m : S.O)⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem m.2 hy) (S.Mbar.inv_mem m.2)
  have hpermx : T.perm ⟨(m : S.O) * y * (m : S.O)⁻¹, hxM⟩ i0 = i0 := hperm
  exact Subgroup.mem_inf.mpr
    ⟨hxM, (T.mem_normalizer_iff ⟨(m : S.O) * y * (m : S.O)⁻¹, hxM⟩ i0).mpr hpermx⟩

theorem s2Rel_index_le (i0 : Fin 3) :
    (S.Mbar ⊓ normalizer (zpowers (eb T.σ i0) : Set S.O)).relIndex S.Mbar ≤ 3 := by
  letI : MulAction S.Mbar (Fin 3) := MulAction.compHom (Fin 3) T.perm
  have hstab : (S.Mbar ⊓ normalizer (zpowers (eb T.σ i0) : Set S.O)).subgroupOf
      S.Mbar = MulAction.stabilizer S.Mbar i0 := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨-, hx⟩
      exact (T.mem_normalizer_iff x i0).mp hx
    · intro h
      exact ⟨x.2, (T.mem_normalizer_iff x i0).mpr h⟩
  have hidx : (S.Mbar ⊓ normalizer (zpowers (eb T.σ i0) : Set S.O)).relIndex
      S.Mbar = (MulAction.stabilizer S.Mbar i0).index := by
    rw [Subgroup.relIndex, hstab]
  rw [hidx, MulAction.index_stabilizer]
  calc (MulAction.orbit S.Mbar i0).ncard
      ≤ (Set.univ : Set (Fin 3)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
    _ = 3 := by rw [Set.ncard_univ, Nat.card_fin]

theorem s2Rel_stab_le (H : Hyp4 S g) (i0 : Fin 3) :
    ∀ y ∈ S.Mbar, ∀ a ∈ Vt S g (T.l i0), a ≠ 0 →
      ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a ∈
        Submodule.span (ZMod 2)
          {a, ((eb T.σ i0 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a} →
      ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (((eb T.σ i0 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a) ∈
        Submodule.span (ZMod 2)
          {a, ((eb T.σ i0 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a} →
      y ∈ S.Mbar ⊓ normalizer (zpowers (eb T.σ i0) : Set S.O) := by
  classical
  intro y hy a ha hane hy1 hy2
  by_contra hnot
  obtain ⟨s, hs0, hconj⟩ := T.conj_e ⟨y, hy⟩ i0
  set j : Fin 3 := T.perm ⟨y, hy⟩ i0 with hj
  have hpi : j ≠ i0 := by
    intro hpi0
    exact hnot ⟨hy, (T.mem_normalizer_iff ⟨y, hy⟩ i0).mpr hpi0⟩
  set k : S.O := eb T.σ i0 with hk
  set t : S.O := T.l i0 with ht
  set k' : S.O := y * k * y⁻¹ with hk'
  have hk'eq : k' = T.σ (Multiplicative.ofAdd (Pi.single j s)) := by
    rw [hk']
    exact hconj
  let κ : S.Qt ≃ₗ[ZMod 2] S.Qt := (k : S.O)
  let κ' : S.Qt ≃ₗ[ZMod 2] S.Qt := (k' : S.O)
  let τ : S.Qt ≃ₗ[ZMod 2] S.Qt := (t : S.O)
  let Y : S.Qt ≃ₗ[ZMod 2] S.Qt := (y : S.O)
  have hκfpf : ∀ v : S.Qt, κ v = v → v = 0 := by
    intro v hv
    exact T.e_fpf i0 v (by simpa [κ, hk] using hv)
  have hκ3 : κ * κ * κ = 1 := by
    have hpow : ((eb T.σ i0 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ 3 = 1 := by
      simpa using congrArg (fun z : S.O => (z : S.Qt ≃ₗ[ZMod 2] S.Qt))
        (T.e_pow_three i0)
    simpa [κ, hk, pow_succ, pow_two] using hpow
  have hκinv : κ⁻¹ = κ * κ := by
    refine inv_eq_of_mul_eq_one_right ?_
    simpa [mul_assoc] using hκ3
  have hchar : ∀ v : S.Qt, v + v = 0 := fun v => by
    rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 2) 2, ZMod.natCast_self, zero_smul]
  have hκrel_all : ∀ v : S.Qt, κ (κ v) + κ v + v = 0 := by
    intro v
    have hfix : κ (κ (κ v) + κ v + v) = κ (κ v) + κ v + v := by
      rw [map_add, map_add]
      have h3 : κ (κ (κ v)) = v := by
        have := congrArg (fun e : S.Qt ≃ₗ[ZMod 2] S.Qt => e v) hκ3
        simpa [LinearEquiv.mul_apply] using this
      rw [h3]
      abel
    exact hκfpf _ hfix
  have hκrel : κ (κ a) = a + κ a := by
    have h := hκrel_all a
    have h2 : κ (κ a) + κ a = a := by
      have h1 : (κ (κ a) + κ a + a) + a = 0 + a := by rw [h]
      rwa [add_assoc, hchar a, add_zero, zero_add] at h1
    calc κ (κ a) = (κ (κ a) + κ a) + κ a := by
          rw [add_assoc, hchar (κ a), add_zero]
      _ = a + κ a := by rw [h2]
  have htN : t ∈ Nbar S g t := S6.self_mem_Nbar H (T.l_mem i0)
  have hτa : τ a = a := by
    simpa [τ, ht] using (mem_Nbar.mp htN).2 a ha
  have hτκinv : τ * κ * τ⁻¹ = κ⁻¹ := by
    have h := congrArg (fun z : S.O => (z : S.Qt ≃ₗ[ZMod 2] S.Qt))
      (T.l_conj_e i0)
    simpa [τ, κ, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hτκ' : τ * κ' * τ⁻¹ = κ' := by
    have hneg : negAt i0 (Pi.single j s) = Pi.single j s := by
      funext l
      by_cases hl : l = i0
      · subst hl
        simp [negAt, Pi.single_eq_of_ne (Ne.symm hpi)]
      · simp [negAt, hl]
    have h := T.basis.act i0 (Pi.single j s)
    rw [hneg] at h
    have h' := congrArg (fun z : S.O => (z : S.Qt ≃ₗ[ZMod 2] S.Qt)) h
    simpa [τ, κ', hk'eq, Subgroup.coe_mul, Subgroup.coe_inv] using h'
  have hτcomm : τ * κ' = κ' * τ := by
    have h := congrArg (fun e : S.Qt ≃ₗ[ZMod 2] S.Qt => e * τ) hτκ'
    simpa [mul_assoc] using h
  have hκ'fpf : ∀ v : S.Qt, κ' v = v → v = 0 := by
    intro v hv
    have hc : ∃ i, (Pi.single j s : Fin 3 → ZMod 3) i ≠ 0 ∧
        ∀ l, l ≠ i → (Pi.single j s : Fin 3 → ZMod 3) l = 0 :=
      ⟨j, by simpa using hs0, fun l hl => by simp [Pi.single_eq_of_ne hl]⟩
    exact (T.fpf_iff (Pi.single j s)).mpr hc v (by simpa [κ', hk'eq] using hv)
  let P : Submodule (ZMod 2) S.Qt := Submodule.span (ZMod 2) ({a, κ a} : Set S.Qt)
  have haP : a ∈ P := Submodule.subset_span (by simp)
  have hκa : κ a ∈ P := Submodule.subset_span (by simp)
  have hκP : ∀ v ∈ P, κ v ∈ P := by
    intro v hv
    obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.mp hv
    rw [map_add, map_smul, map_smul]
    refine P.add_mem (P.smul_mem _ hκa) (P.smul_mem _ ?_)
    rw [hκrel]
    exact P.add_mem haP hκa
  have hτka : τ (κ a) = a + κ a := by
    have hτκ : τ * κ = κ⁻¹ * τ := by
      have h := congrArg (fun e : S.Qt ≃ₗ[ZMod 2] S.Qt => e * τ) hτκinv
      simpa [mul_assoc] using h
    calc τ (κ a) = (τ * κ) a := (LinearEquiv.mul_apply τ κ a).symm
      _ = (κ⁻¹ * τ) a := by rw [hτκ]
      _ = κ⁻¹ (τ a) := LinearEquiv.mul_apply κ⁻¹ τ a
      _ = κ⁻¹ a := by rw [hτa]
      _ = (κ * κ) a := by rw [hκinv]
      _ = κ (κ a) := LinearEquiv.mul_apply κ κ a
      _ = a + κ a := hκrel
  have hτP : ∀ v ∈ P, τ v ∈ P := by
    intro v hv
    obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.mp hv
    rw [map_add, map_smul, map_smul, hτa, hτka]
    exact P.add_mem (P.smul_mem _ haP) (P.smul_mem _ (P.add_mem haP hκa))
  have hYP : ∀ v ∈ P, Y v ∈ P := by
    intro v hv
    obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.mp hv
    rw [map_add, map_smul, map_smul]
    exact P.add_mem (P.smul_mem _ (by simpa [P, Y, κ] using hy1))
      (P.smul_mem _ (by simpa [P, Y, κ] using hy2))
  have hYsurj : ∀ v ∈ P, ∃ w ∈ P, Y w = v := by
    intro v hv
    let f : P → P := fun z => ⟨Y z, hYP z z.2⟩
    have hf : Function.Injective f :=
      fun z1 z2 h => Subtype.ext (Y.injective (congrArg Subtype.val h))
    have hsurj := Finite.injective_iff_surjective.mp hf
    obtain ⟨z, hz⟩ := hsurj ⟨v, hv⟩
    exact ⟨z, z.2, congrArg Subtype.val hz⟩
  obtain ⟨b, hbP, hbY⟩ := hYsurj a haP
  have hYinva : Y⁻¹ a = b := by
    rw [← hbY]
    exact LinearEquiv.symm_apply_apply Y b
  have hk'a : κ' a ∈ P := by
    have h1 : κ' a = Y (κ (Y⁻¹ a)) := by
      dsimp only [κ', Y, κ]
      rw [hk']
      rfl
    rw [h1, hYinva]
    exact hYP (κ b) (hκP b hbP)
  have hτk'a : τ (κ' a) = κ' a := by
    calc τ (κ' a) = (τ * κ') a := (LinearEquiv.mul_apply τ κ' a).symm
      _ = (κ' * τ) a := by rw [hτcomm]
      _ = κ' (τ a) := LinearEquiv.mul_apply κ' τ a
      _ = κ' a := by rw [hτa]
  have hk'a_span : κ' a ∈ Submodule.span (ZMod 2) ({a} : Set S.Qt) := by
    obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp hk'a
    have hfix : τ (r • a + s • κ a) = r • a + s • κ a := by
      rw [hrs]
      exact hτk'a
    rw [map_add, map_smul, map_smul, hτa, hτka, smul_add] at hfix
    have hs : s = 0 := by
      have h1 : s • a + s • κ a = s • κ a := add_left_cancel hfix
      have h2 : s • a + s • κ a = 0 + s • κ a := by rw [zero_add]; exact h1
      have h3 : s • a = 0 := add_right_cancel h2
      exact (smul_eq_zero.mp h3).resolve_right hane
    rw [← hrs, hs]
    simpa using Submodule.smul_mem (Submodule.span (ZMod 2) ({a} : Set S.Qt)) r
      (Submodule.subset_span (by simp : a ∈ ({a} : Set S.Qt)))
  have hk'a_ne : κ' a ≠ 0 := by
    intro h0
    have h1 : κ' a = κ' 0 := by simpa using h0
    exact hane (κ'.injective h1)
  have hk'a_eq : κ' a = a := by
    rcases S4.mem_span_cl_iff.mp hk'a_span with h0 | h1
    · exact absurd h0 hk'a_ne
    · exact h1
  exact hane (hκ'fpf a hk'a_eq)

theorem s2Rel (H : Hyp4 S g) (i0 : Fin 3)
    (htrans : ∀ k : Fin 3, ∃ x : S.Mbar, T.perm x k ≠ k) :
    Smith1980Orth.S2Rel S g (T.l i0) (eb T.σ i0)
      (S.Mbar ⊓ normalizer (zpowers (eb T.σ i0) : Set S.O)) :=
  ⟨inf_le_left,
    ⟨T.e_mem_Mbar i0, Subgroup.le_normalizer (Subgroup.mem_zpowers (eb T.σ i0))⟩,
    T.s2Rel_cent_le i0,
    T.s2Rel_orbit H i0,
    T.s2Rel_inv_conj i0 htrans,
    T.s2Rel_index_le i0,
    T.s2Rel_stab_le H i0⟩

end TriData

end CFSG.GF2Type.Smith1979.TriPlus

end
