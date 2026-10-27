module

public import CFSG.LargeExtraspecial.S12Defs
public import CFSG.LargeExtraspecial.S12Six

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

@[expose] def IsReducible12 : Prop :=
  ∃ W : Submodule (ZMod 2) S.Qt, W ≠ ⊥ ∧ W ≠ ⊤ ∧
    ∀ m : S.M, ∀ v ∈ W, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W

theorem s12_isReducible12_of_orbit {v : S.Qt} (hv : v ≠ 0)
    (h : ∀ m : S.M, polar S.q v ((S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = 0) : S.IsReducible12 := by
  set W := Submodule.span (ZMod 2) (Set.range fun m : S.M => (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
  have hvW : v ∈ W := Submodule.subset_span ⟨1, by simp⟩
  have hinv : ∀ m : S.M, ∀ w ∈ W, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W := by
    intro m w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨m', rfl⟩ := hw
      refine Submodule.subset_span ⟨m * m', ?_⟩
      simp [map_mul, LinearEquiv.mul_apply]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact W.smul_mem c hx
  have hpol0 : ∀ m₁ m₂ : S.M, polar S.q ((S.ρ m₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
      ((S.ρ m₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = 0 := by
    intro m₁ m₂
    have e := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ m₁⁻¹).2
      ((S.ρ m₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) ((S.ρ m₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
    rw [← e]
    have e1 : (S.ρ m₁⁻¹ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.ρ m₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← map_mul, inv_mul_cancel, map_one]
      rfl
    have e2 : (S.ρ m₁⁻¹ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.ρ m₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
        (S.ρ (m₁⁻¹ * m₂) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
      rw [map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply]
    rw [e1, e2]
    exact h _
  have hpol : ∀ x ∈ W, ∀ y ∈ W, polar S.q x y = 0 := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m₁, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨m₂, rfl⟩ := hy
        exact hpol0 m₁ m₂
      | zero => simp
      | add y y' _ _ h1 h2 => rw [polar_add_right, h1, h2, add_zero]
      | smul c y _ h1 => rw [polar_smul_right, h1, smul_zero]
    | zero => simp
    | add x x' _ _ h1 h2 => rw [polar_add_left, h1, h2, add_zero]
    | smul c x _ h1 => rw [polar_smul_left, h1, smul_zero]
  refine ⟨W, fun hb => hv ?_, fun ht => hv ?_, hinv⟩
  · rw [hb] at hvW
    exact (Submodule.mem_bot _).mp hvW
  · refine S.q_nondegenerate.1 v fun y => ?_
    have := hpol v hvW y (ht ▸ Submodule.mem_top)
    simpa using this

theorem s12_commute_of_mem_Lbar_normalizer {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) (h : S.M) {x : S.O}
    (hx : x ∈ S.Lbar ((h : G) * g)) (hxN : x ∈ normalizer (S.Lbar g : Set S.O)) (hx1 : x ≠ 1) :
    (g * S.z * g⁻¹) * (((h : G) * g) * S.z * ((h : G) * g)⁻¹) =
      (((h : G) * g) * S.z * ((h : G) * g)⁻¹) * (g * S.z * g⁻¹) := by
  set a := g * S.z * g⁻¹ with ha
  set g' := (h : G) * g with hg'
  set b := g' * S.z * g'⁻¹ with hb
  obtain ⟨hbQ, hbne⟩ := S.s12_conj_mem haQ hne h
  by_contra hab
  have hcomm : a * b * a⁻¹ * b⁻¹ = S.z := by
    rcases S.commutator_eq_one_or_z haQ hbQ with h1 | h1
    · exact absurd (by
        calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
          _ = b * a := by rw [h1, one_mul]) hab
    · exact h1
  obtain ⟨y, hy, rfl⟩ := S.s12_mem_Lbar.mp hx
  have hyM : y ∈ S.M := S.L0_le_M g' hy
  have hfix := (S.timmesfeld_12_4_1 haQ hne hn ⟨y, hyM⟩).mp hxN
  rw [S.ρ_cl _ haQ] at hfix
  change S.cl (y * a * y⁻¹) = S.cl a at hfix
  have ha2 : a * a = 1 := by rw [← pow_two]; exact S.s12_conj_z_sq g
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hay : a * y * a⁻¹ = y ∨ a * y * a⁻¹ = S.z * y := by
    rcases (S.cl_eq_cl_iff haQ (S.conj_mem_QG hyM haQ)).mp hfix.symm with h1 | h1
    · left
      have hya : y * a = a * y := by
        calc y * a = y * a * y⁻¹ * y := by group
          _ = a * y := by rw [h1]
      calc a * y * a⁻¹ = y * a * a⁻¹ := by rw [← hya]
        _ = y := by group
    · right
      have hya : y * a = a * S.z * y := by
        calc y * a = y * a * y⁻¹ * y := by group
          _ = a * S.z * y := by rw [h1]
      have e : a * y * a⁻¹ = a⁻¹ * y * a := by rw [hainv]
      calc a * y * a⁻¹ = a⁻¹ * y * a := e
        _ = a⁻¹ * (y * a) := by group
        _ = a⁻¹ * (a * S.z * y) := by rw [hya]
        _ = S.z * y := by group
  have hzb : S.z ∈ S.Qa g' := S.z_mem_Qa_of_mem_QG rfl hbQ hbne
  have hyQbz : y ∈ S.Qa (a * g') := by
    rw [S.s12_Qa_mul]
    rcases hay with h1 | h1
    · exact ⟨y, hy.1, by simpa [MulAut.conj_apply] using h1⟩
    · have hz' : S.z ∈ (S.Qa g').map (MulAut.conj a).toMonoidHom :=
        ⟨S.z, hzb, by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [S.z_comm_QG haQ]
          group⟩
      have hay' : a * y * a⁻¹ ∈ (S.Qa g').map (MulAut.conj a).toMonoidHom := ⟨y, hy.1, rfl⟩
      rw [h1] at hay'
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hz') hay'
      simpa using this
  set T := S.conjBy g' with hT
  have hz1 : S.z ≠ 1 := S.z_ne_one
  obtain ⟨w, hwQ, hw⟩ := T.exists_conj_eq_mul_z hzb hz1 hbne.symm
  have hwb : w * b = b * w := T.z_comm_QG hwQ
  have hbz : b * S.z = S.z * b := S.z_comm_QG hbQ
  have hb2 : b * b = 1 := by rw [← pow_two]; exact S.s12_conj_z_sq g'
  have habz : (a * g') * S.z * (a * g')⁻¹ = b * S.z := by
    calc (a * g') * S.z * (a * g')⁻¹ = a * b * a⁻¹ := by rw [hb]; group
      _ = a * b * a⁻¹ * b⁻¹ * b := by group
      _ = S.z * b := by rw [hcomm]
      _ = b * S.z := hbz.symm
  have hwz : (w * (a * g')) * S.z * (w * (a * g'))⁻¹ = 1 * S.z * 1⁻¹ := by
    calc (w * (a * g')) * S.z * (w * (a * g'))⁻¹ = w * ((a * g') * S.z * (a * g')⁻¹) * w⁻¹ := by
          group
      _ = w * b * w⁻¹ * (w * S.z * w⁻¹) := by rw [habz]; group
      _ = b * (S.z * T.z) := by rw [hwb, hw]; group
      _ = S.z * (b * b) := by
          change b * (S.z * b) = S.z * (b * b)
          rw [← mul_assoc, hbz, mul_assoc]
      _ = 1 * S.z * 1⁻¹ := by rw [hb2]; group
  have hQ : S.Qa (w * (a * g')) = S.QG := by rw [S.Qa_eq_of_conj_eq hwz, S.Qa_one]
  have hwy : w * y * w⁻¹ ∈ S.QG := by
    rw [← hQ, S.s12_Qa_mul]
    exact ⟨y, hyQbz, rfl⟩
  have hyQ : y ∈ S.QG := by
    rcases T.commutator_eq_one_or_z hwQ hy.1 with h1 | h1
    · have : w * y * w⁻¹ = y := by
        calc w * y * w⁻¹ = w * y * w⁻¹ * y⁻¹ * y := by group
          _ = y := by rw [h1, one_mul]
      rwa [this] at hwy
    · have : y = b⁻¹ * (w * y * w⁻¹) := by
        calc y = (w * y * w⁻¹ * y⁻¹)⁻¹ * (w * y * w⁻¹) := by group
          _ = b⁻¹ * (w * y * w⁻¹) := by rw [h1]; rfl
      rw [this]
      exact S.QG.mul_mem (S.QG.inv_mem hbQ) hwy
  exact hx1 ((S.ρ_eq_one_iff _).mpr hyQ)

theorem s12_polar_eq_zero_of_mem_commSpace {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {q : QuadraticForm (ZMod 2) V} {t : V ≃ₗ[ZMod 2] V} {l : ℕ} (ht : IsTypeA q t l) {u v : V}
    (hu : u ∈ commSpace t) (hv : v ∈ commSpace t) : polar q u v = 0 := by
  rw [polar, ht.2.2.2.2 _ (Submodule.add_mem _ hu hv), ht.2.2.2.2 _ hu, ht.2.2.2.2 _ hv]
  simp

theorem s12_coe_conj (m t : S.O) :
    ((m * t * m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (m : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (m : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ := by
  simp

theorem s12_isReducible12_of_fuse {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hC : ∀ m ∈ S.Mbar, m * t * m⁻¹ = t →
      (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    (h3 : ∀ m ∈ S.Mbar, orderOf (t * (m * t * m⁻¹)) = 1 ∨ orderOf (t * (m * t * m⁻¹)) = 2 ∨
      orderOf (t * (m * t * m⁻¹)) = 3) :
    S.IsReducible12 := by
  set a := g * S.z * g⁻¹ with ha
  have ha0 := S.s12_cl_ne_zero_of_conj haQ hne
  have hqa : S.q (S.cl a) = 0 := (S.q_cl_eq_zero_iff haQ).mpr (S.s12_conj_z_sq g)
  have htt : t * t = 1 := Subtype.ext htA.2.2.1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  refine S.s12_isReducible12_of_orbit ha0 fun h => ?_
  set m := S.ρ h with hm
  have hmM : m ∈ S.Mbar := ⟨h, rfl⟩
  set x := m * t * m⁻¹ with hx
  obtain ⟨hbQ, hbne⟩ := S.s12_conj_mem haQ hne h
  have hmcl : (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl a) =
      S.cl (((h : G) * g) * S.z * ((h : G) * g)⁻¹) := by
    rw [hm, S.ρ_cl h haQ, S.s12_mul_conj_z]
  have hxA : IsTypeA S.q (x : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := by
    rw [hx, S.s12_coe_conj]
    exact s12_isTypeA_conj htA m.2
  have hxx : x * x = 1 := Subtype.ext hxA.2.2.1
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxM : x ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hmM (S.Lbar_le_Mbar g ht)) (S.Mbar.inv_mem hmM)
  rcases h3 m hmM with h1 | h1 | h1
  ·
    have hxt : x = t := by
      have := orderOf_eq_one_iff.mp h1
      calc x = t⁻¹ * (t * x) := by group
        _ = t := by rw [this, mul_one, htinv]
    rw [hC m hmM hxt, QuadraticMap.polar_self, hqa, smul_zero]
  ·
    have hcomm : x * t = t * x := by
      have h1' : orderOf (t * x) = 2 := h1
      have h2 : (t * x) ^ 2 = 1 := by
        have := pow_orderOf_eq_one (t * x)
        rwa [h1'] at this
      calc x * t = x⁻¹ * t⁻¹ := by rw [hxinv, htinv]
        _ = (t * x)⁻¹ := by group
        _ = t * x := by
          rw [inv_eq_of_mul_eq_one_right (show t * x * (t * x) = 1 by rw [← pow_two]; exact h2)]
    have hxfix := hC x hxM (by rw [hxinv, mul_assoc, ← hcomm, ← mul_assoc, hxx, one_mul])
    obtain ⟨h', hh'⟩ := hxM
    have hxN : x ∈ normalizer (S.Lbar g : Set S.O) := by
      rw [← hh'] at hxfix ⊢
      exact (S.timmesfeld_12_4_1 haQ hne hn h').mpr hxfix
    have hxL : x ∈ S.Lbar ((h : G) * g) := by
      rw [S.s12_Lbar_mul]
      exact ⟨t, ht, rfl⟩
    have hx1 : x ≠ 1 := fun e => hxA.2.1 (by rw [e]; rfl)
    have hab := S.s12_commute_of_mem_Lbar_normalizer haQ hne hn h hxL hxN hx1
    rw [hmcl]
    exact (S.polar_cl_eq_zero_iff haQ hbQ).mpr hab
  ·
    have h1' : orderOf (t * x) = 3 := h1
    have h3' : (t * x) ^ 3 = 1 := by
      have := pow_orderOf_eq_one (t * x)
      rwa [h1'] at this
    have hbraid : x * t * x⁻¹ = (t * m) * t * (t * m)⁻¹ := by
      have e : t * x * t = x * t * x := by
        have := congrArg (fun y => x⁻¹ * t⁻¹ * y * x⁻¹) h3'
        simp only [pow_succ, pow_zero, one_mul] at this
        calc t * x * t = x⁻¹ * t⁻¹ * (t * x * (t * x) * (t * x)) * x⁻¹ := by group
          _ = x⁻¹ * t⁻¹ * 1 * x⁻¹ := by rw [← this]
          _ = x * t * x := by rw [hxinv, htinv]; group
      calc x * t * x⁻¹ = x * t * x := by rw [hxinv]
        _ = t * x * t := e.symm
        _ = (t * m) * t * (t * m)⁻¹ := by rw [hx, mul_inv_rev, htinv]; group
    have hfix2 := hC ((t * m)⁻¹ * x)
      (S.Mbar.mul_mem (S.Mbar.inv_mem (S.Mbar.mul_mem (S.Lbar_le_Mbar g ht) hmM)) hxM)
      (by
        calc (t * m)⁻¹ * x * t * ((t * m)⁻¹ * x)⁻¹ = (t * m)⁻¹ * (x * t * x⁻¹) * (t * m) := by
              group
          _ = t := by rw [hbraid]; group)
    have hxp : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl a) =
        (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl a)) := by
      have e : x = (t * m) * ((t * m)⁻¹ * x) := by group
      rw [e, Subgroup.coe_mul, LinearEquiv.mul_apply, hfix2, Subgroup.coe_mul,
        LinearEquiv.mul_apply]
    set p₁ := S.cl a
    set p₂ := (m : S.Qt ≃ₗ[ZMod 2] S.Qt) p₁
    have hq2 : S.q p₂ = 0 := by
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup m.2]
      exact hqa
    have hq2' : S.q ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) p₂) = 0 := by
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup t.2]
      exact hq2
    have hA : S.q ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) p₂ - p₁) = 0 := by
      rw [← hxp]
      exact hxA.2.2.2.2 _ (sub_mem_commSpace _ _)
    have hpol1 : polar S.q p₁ ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) p₂) = 0 := by
      rw [OrthoF2.vec_sub] at hA
      rw [QuadraticMap.polar_comm, polar, hA, hq2', hqa]
      simp
    have hp₁ : p₁ ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := (S.timmesfeld_12_6 haQ hne ht htA).1
    have hpol2 : polar S.q p₁ ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) p₂ - p₂) = 0 :=
      s12_polar_eq_zero_of_mem_commSpace htA hp₁ (sub_mem_commSpace _ _)
    rw [polar_sub_right, hpol1, zero_sub, neg_eq_zero] at hpol2
    exact hpol2

end Setting

end CFSG.LargeExtraspecial
